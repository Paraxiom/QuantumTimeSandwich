//! egui UI: 3D torus, engine cycle visualization, charts, sliders, results readout.
//! Two-tab layout: Vacuum Engine and CNT Doppler cooling.

use std::f32::consts::PI;

use eframe::egui;
use egui_plot::{Bar, BarChart, Corner, Legend, Line, MarkerShape, Plot, PlotPoint, PlotPoints,
    Points, Polygon, Text as PlotText, VLine};

use crate::cnt_bridge::{self, ChartData, LatticeSnapshot};
use crate::cnt_physics::{PhysicsParams, PhysicsResult};
use crate::covariant::{DescentResult, DescentStep, TorusPoint};
use crate::engine::{EngineConfig, EngineResult};
use crate::logit_drift::{self, DriftConfig, DriftResult, MaskHeatmap as DriftHeatmap,
    DriftAnalysisResult, MaskAnalysisResult};
use crate::sim_worker::{ScalingEntry, SimRequest, SimResponse, SimWorker};
use topological_coherence::MaskType;

// ─── Colors ──────────────────────────────────────────────────────────────────

const FOREST_GREEN: egui::Color32 = egui::Color32::from_rgb(86, 166, 96);
const WARN_RED: egui::Color32 = egui::Color32::from_rgb(217, 77, 77);
const DIM: egui::Color32 = egui::Color32::from_rgb(160, 160, 150);
const GOLD_EG: egui::Color32 = egui::Color32::from_rgb(212, 175, 55);
const HEADING_CLR: egui::Color32 = egui::Color32::from_rgb(220, 218, 210);
const LABEL_CLR: egui::Color32 = egui::Color32::from_rgb(230, 228, 218);
const TORUS_WIRE: egui::Color32 = egui::Color32::from_rgb(60, 125, 85);

const COMPRESS_BLUE: egui::Color32 = egui::Color32::from_rgb(70, 130, 230);
const EXTRACT_GOLD: egui::Color32 = egui::Color32::from_rgb(255, 200, 50);
const EXPAND_GREEN: egui::Color32 = egui::Color32::from_rgb(100, 200, 120);
const LOSS_RED: egui::Color32 = egui::Color32::from_rgb(230, 70, 70);
const THERMAL_ORANGE: egui::Color32 = egui::Color32::from_rgb(255, 140, 50);

const X_ERROR_RED: egui::Color32 = egui::Color32::from_rgb(230, 70, 70);
const Z_ERROR_BLUE: egui::Color32 = egui::Color32::from_rgb(70, 130, 230);
const Y_ERROR_PURPLE: egui::Color32 = egui::Color32::from_rgb(190, 70, 190);
const E_PARTICLE_ORANGE: egui::Color32 = egui::Color32::from_rgb(255, 170, 30);

// ─── Tab enum ────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tab {
    VacuumEngine,
    CntDoppler,
    HallucinationReduction,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DriftVizMode {
    Overview,
    DriftAnalysis,
    MaskAnalysis,
}

// ─── Visuals ─────────────────────────────────────────────────────────────────

fn forest_visuals() -> egui::Visuals {
    let mut vis = egui::Visuals::dark();
    vis.panel_fill = egui::Color32::from_rgb(24, 30, 24);
    vis.window_fill = egui::Color32::from_rgb(28, 34, 28);
    vis.extreme_bg_color = egui::Color32::from_rgb(20, 24, 20);
    vis.faint_bg_color = egui::Color32::from_rgb(34, 44, 34);
    vis.widgets.inactive.bg_fill = egui::Color32::from_rgb(50, 65, 50);
    vis.widgets.hovered.bg_fill = egui::Color32::from_rgb(65, 90, 65);
    vis.widgets.active.bg_fill = FOREST_GREEN;
    vis.override_text_color = Some(LABEL_CLR);
    vis
}

fn dim_label(ui: &mut egui::Ui, text: &str) {
    ui.colored_label(DIM, text);
}

fn section_heading(ui: &mut egui::Ui, text: &str) {
    ui.add_space(4.0);
    ui.horizontal(|ui| {
        let (rect, _) = ui.allocate_exact_size(egui::vec2(3.0, 16.0), egui::Sense::hover());
        ui.painter().rect_filled(rect, 1.0, GOLD_EG);
        ui.add_space(4.0);
        ui.colored_label(HEADING_CLR, egui::RichText::new(text).strong().size(14.0));
    });
    ui.separator();
}

// ─── Length formatting ───────────────────────────────────────────────────────

fn format_length(meters: f64) -> String {
    if meters >= 1e-2 {
        format!("{:.2} cm", meters * 1e2)
    } else if meters >= 1e-3 {
        format!("{:.2} mm", meters * 1e3)
    } else if meters >= 1e-6 {
        format!("{:.1} \u{03bc}m", meters * 1e6)
    } else {
        format!("{:.1} nm", meters * 1e9)
    }
}

fn format_freq(hz: f64) -> String {
    let omega_over_2pi = hz / (2.0 * std::f64::consts::PI);
    if omega_over_2pi >= 1e15 {
        format!("{:.2} PHz", omega_over_2pi / 1e15)
    } else if omega_over_2pi >= 1e12 {
        format!("{:.2} THz", omega_over_2pi / 1e12)
    } else if omega_over_2pi >= 1e9 {
        format!("{:.2} GHz", omega_over_2pi / 1e9)
    } else if omega_over_2pi >= 1e6 {
        format!("{:.2} MHz", omega_over_2pi / 1e6)
    } else {
        format!("{:.2e} Hz", omega_over_2pi)
    }
}

// ─── 3-D → 2-D projection helpers ───────────────────────────────────────────

fn torus_pt(r_maj: f32, r_min: f32, u: f32, v: f32) -> [f32; 3] {
    [
        (r_maj + r_min * v.cos()) * u.cos(),
        (r_maj + r_min * v.cos()) * u.sin(),
        r_min * v.sin(),
    ]
}

fn project(pos: [f32; 3], rot: [f32; 2], rect: egui::Rect) -> (egui::Pos2, f32) {
    let (sx, cx) = rot[0].sin_cos();
    let (sy, cy) = rot[1].sin_cos();
    let x = pos[0] * cy + pos[2] * sy;
    let y = pos[0] * sx * sy + pos[1] * cx - pos[2] * sx * cy;
    let z = -pos[0] * cx * sy + pos[1] * sx + pos[2] * cx * cy;
    let size = rect.width().min(rect.height()) * 0.28;
    let c = rect.center();
    (egui::pos2(c.x + x * size, c.y - y * size), z)
}

fn depth_alpha(z: f32) -> u8 {
    let t = ((z + 2.0) / 4.0).clamp(0.0, 1.0);
    (25.0 + 170.0 * t) as u8
}

// ─── CNT error color helper ─────────────────────────────────────────────────

fn error_color(has_x: bool, has_z: bool) -> egui::Color32 {
    match (has_x, has_z) {
        (true, true) => Y_ERROR_PURPLE,
        (true, false) => X_ERROR_RED,
        (false, true) => Z_ERROR_BLUE,
        _ => egui::Color32::from_rgba_unmultiplied(86, 166, 96, 60),
    }
}

// ─── Engine cycle phase ──────────────────────────────────────────────────────

#[derive(Clone, Copy)]
enum CyclePhase {
    Compress,
    Extract,
    Expand,
    Idle,
}

fn cycle_phase(time: f32) -> (CyclePhase, f32) {
    let t = (time * 0.3).rem_euclid(4.0);
    if t < 1.0 {
        (CyclePhase::Compress, t)
    } else if t < 2.0 {
        (CyclePhase::Extract, t - 1.0)
    } else if t < 3.0 {
        (CyclePhase::Expand, t - 2.0)
    } else {
        (CyclePhase::Idle, t - 3.0)
    }
}

fn phase_color(phase: CyclePhase, frac: f32) -> (u8, u8, u8) {
    let pulse = 0.5 + 0.5 * (frac * PI * 2.0).sin();
    match phase {
        CyclePhase::Compress => {
            let r = (40.0 + 30.0 * pulse) as u8;
            let g = (60.0 + 40.0 * pulse) as u8;
            let b = (140.0 + 80.0 * pulse) as u8;
            (r, g, b)
        }
        CyclePhase::Extract => {
            let r = (180.0 + 60.0 * pulse) as u8;
            let g = (150.0 + 40.0 * pulse) as u8;
            let b = (30.0 + 20.0 * pulse) as u8;
            (r, g, b)
        }
        CyclePhase::Expand => {
            let r = (50.0 + 40.0 * pulse) as u8;
            let g = (140.0 + 60.0 * pulse) as u8;
            let b = (60.0 + 30.0 * pulse) as u8;
            (r, g, b)
        }
        CyclePhase::Idle => {
            let v = (50.0 + 20.0 * pulse) as u8;
            (v, v, v)
        }
    }
}

fn phase_minor_radius(phase: CyclePhase, frac: f32, base: f32) -> f32 {
    match phase {
        CyclePhase::Compress => base * (1.0 - 0.08 * frac),
        CyclePhase::Extract => base * 0.92,
        CyclePhase::Expand => base * (0.92 + 0.08 * frac),
        CyclePhase::Idle => base,
    }
}

// ─── Draw the rotating torus with covariant descent paths (Vacuum Engine) ───

fn draw_engine_torus(
    painter: &egui::Painter,
    rect: egui::Rect,
    rot: [f32; 2],
    grid_n: usize,
    time: f32,
    descent_cov: Option<&[DescentStep]>,
    descent_euc: Option<&[DescentStep]>,
    show_euclidean: bool,
) {
    let rm = 1.2_f32;
    let (phase, phase_frac) = cycle_phase(time);
    let rn = phase_minor_radius(phase, phase_frac, 0.45);
    let (pr, pg, pb) = phase_color(phase, phase_frac);
    let rings = 24_usize;
    let segs = 48_usize;

    // Surface patches (front-facing only)
    for ring in 0..rings {
        let u0 = 2.0 * PI * ring as f32 / rings as f32;
        let u1 = 2.0 * PI * ((ring + 1) % rings) as f32 / rings as f32;
        for s in 0..segs {
            let v0 = 2.0 * PI * s as f32 / segs as f32;
            let v1 = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;

            let (p00, z00) = project(torus_pt(rm, rn, u0, v0), rot, rect);
            let (p10, z10) = project(torus_pt(rm, rn, u1, v0), rot, rect);
            let (p11, z11) = project(torus_pt(rm, rn, u1, v1), rot, rect);
            let (p01, z01) = project(torus_pt(rm, rn, u0, v1), rot, rect);

            let avg_z = (z00 + z10 + z11 + z01) * 0.25;

            let e1x = p10.x - p00.x;
            let e1y = p10.y - p00.y;
            let e2x = p01.x - p00.x;
            let e2y = p01.y - p00.y;
            let cross = e1x * e2y - e1y * e2x;
            if cross > 0.0 {
                continue;
            }

            let depth_t = ((avg_z + 2.0) / 4.0).clamp(0.0, 1.0);
            let alpha = (18.0 + 22.0 * depth_t) as u8;
            let r = ((pr as f32 * 0.4 + (20.0 + 50.0 * depth_t) * 0.6)) as u8;
            let g = ((pg as f32 * 0.4 + (60.0 + 80.0 * depth_t) * 0.6)) as u8;
            let b = ((pb as f32 * 0.4 + (50.0 + 30.0 * (1.0 - depth_t)) * 0.6)) as u8;

            let mesh = egui::Mesh {
                indices: vec![0, 1, 2, 0, 2, 3],
                vertices: vec![
                    egui::epaint::Vertex { pos: p00, uv: egui::epaint::WHITE_UV, color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha) },
                    egui::epaint::Vertex { pos: p10, uv: egui::epaint::WHITE_UV, color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha) },
                    egui::epaint::Vertex { pos: p11, uv: egui::epaint::WHITE_UV, color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha) },
                    egui::epaint::Vertex { pos: p01, uv: egui::epaint::WHITE_UV, color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha) },
                ],
                texture_id: egui::TextureId::default(),
            };
            painter.add(egui::Shape::mesh(mesh));
        }
    }

    // Wireframe rings
    for ring in 0..rings {
        let fixed = 2.0 * PI * ring as f32 / rings as f32;
        for s in 0..segs {
            let a = 2.0 * PI * s as f32 / segs as f32;
            let b = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;
            let (s1, z1) = project(torus_pt(rm, rn, fixed, a), rot, rect);
            let (s2, z2) = project(torus_pt(rm, rn, fixed, b), rot, rect);
            let al = depth_alpha((z1 + z2) * 0.5);
            let depth_t = (((z1 + z2) * 0.5 + 2.0) / 4.0).clamp(0.0, 1.0);
            let wr = (TORUS_WIRE.r() as f32 * (0.6 + 0.4 * depth_t)) as u8;
            let wg = (TORUS_WIRE.g() as f32 * (0.6 + 0.4 * depth_t)) as u8;
            let wb = (TORUS_WIRE.b() as f32 * (0.6 + 0.4 * depth_t)) as u8;
            painter.line_segment(
                [s1, s2],
                egui::Stroke::new(0.7, egui::Color32::from_rgba_unmultiplied(wr, wg, wb, al)),
            );
            let (s1, z1) = project(torus_pt(rm, rn, a, fixed), rot, rect);
            let (s2, z2) = project(torus_pt(rm, rn, b, fixed), rot, rect);
            let al = depth_alpha((z1 + z2) * 0.5);
            let depth_t = (((z1 + z2) * 0.5 + 2.0) / 4.0).clamp(0.0, 1.0);
            let wr = (TORUS_WIRE.r() as f32 * (0.6 + 0.4 * depth_t)) as u8;
            let wg = (TORUS_WIRE.g() as f32 * (0.6 + 0.4 * depth_t)) as u8;
            let wb = (TORUS_WIRE.b() as f32 * (0.6 + 0.4 * depth_t)) as u8;
            painter.line_segment(
                [s1, s2],
                egui::Stroke::new(0.7, egui::Color32::from_rgba_unmultiplied(wr, wg, wb, al)),
            );
        }
    }

    // Non-contractible cycles (gold, pulsing)
    for &(cycle_u, fixed_other) in &[(true, 0.0_f32), (true, PI), (false, 0.0), (false, PI)] {
        for s in 0..segs {
            let a = 2.0 * PI * s as f32 / segs as f32;
            let b = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;
            let (p1, p2) = if cycle_u {
                (torus_pt(rm, rn, fixed_other, a), torus_pt(rm, rn, fixed_other, b))
            } else {
                (torus_pt(rm, rn, a, fixed_other), torus_pt(rm, rn, b, fixed_other))
            };
            let (sc1, _) = project(p1, rot, rect);
            let (sc2, _) = project(p2, rot, rect);
            let pulse = 0.55 + 0.45 * (a * 1.0 + time * if cycle_u { -2.0 } else { 1.5 }).sin();
            let r = (212.0 * pulse + 80.0 * (1.0 - pulse)) as u8;
            let g = (175.0 * pulse + 100.0 * (1.0 - pulse)) as u8;
            let bl = (55.0 * pulse + 30.0 * (1.0 - pulse)) as u8;
            painter.line_segment([sc1, sc2], egui::Stroke::new(2.8, egui::Color32::from_rgb(r, g, bl)));
        }
    }

    // Qubit nodes on torus surface
    for row in 0..grid_n {
        for col in 0..grid_n {
            let u = 2.0 * PI * row as f32 / grid_n as f32;
            let v = 2.0 * PI * col as f32 / grid_n as f32;
            let (sp, z) = project(torus_pt(rm, rn + 0.015, u, v), rot, rect);
            let al = depth_alpha(z);
            let phase_v = 0.6 + 0.4 * (time * 2.0 + u + v).sin();
            let br = (210.0 * phase_v) as u8;
            painter.circle_filled(sp, 2.5, egui::Color32::from_rgba_unmultiplied(br, br, (br as f32 * 0.9) as u8, al));
        }
    }

    // DCE photon sparks during extraction phase
    if matches!(phase, CyclePhase::Extract) {
        let spark_count = 12;
        for i in 0..spark_count {
            let spark_u = 2.0 * PI * (i as f32 + time * 5.0).rem_euclid(spark_count as f32) / spark_count as f32;
            let spark_v = 2.0 * PI * (i as f32 * 0.618 + time * 3.0).rem_euclid(1.0);
            let (sp, _z) = project(torus_pt(rm, rn + 0.06, spark_u, spark_v), rot, rect);
            let spark_alpha = (180.0 * phase_frac.min(1.0 - phase_frac) * 2.0) as u8;
            painter.circle_filled(sp, 3.5, egui::Color32::from_rgba_unmultiplied(255, 220, 60, spark_alpha));
            painter.circle_filled(sp, 1.5, egui::Color32::from_rgba_unmultiplied(255, 255, 200, spark_alpha));
        }
    }

    // Covariant descent path
    if let Some(steps) = descent_cov {
        draw_descent_path(painter, rect, rot, rm, rn, steps, true, time);
    }
    if show_euclidean {
        if let Some(steps) = descent_euc {
            draw_descent_path(painter, rect, rot, rm, rn, steps, false, time);
        }
    }
}

fn draw_descent_path(
    painter: &egui::Painter,
    rect: egui::Rect,
    rot: [f32; 2],
    rm: f32,
    rn: f32,
    steps: &[DescentStep],
    is_covariant: bool,
    time: f32,
) {
    if steps.len() < 2 {
        return;
    }
    let max_visible = ((time * 20.0) as usize).min(steps.len());
    if max_visible < 2 {
        return;
    }
    let stride = (max_visible / 200).max(1);

    for i in (stride..max_visible).step_by(stride) {
        let prev = &steps[i - stride];
        let curr = &steps[i];
        let u1 = 2.0 * PI * prev.position.x as f32;
        let v1 = 2.0 * PI * prev.position.y as f32;
        let u2 = 2.0 * PI * curr.position.x as f32;
        let v2 = 2.0 * PI * curr.position.y as f32;
        let (sp1, _) = project(torus_pt(rm, rn + 0.03, u1, v1), rot, rect);
        let (sp2, _) = project(torus_pt(rm, rn + 0.03, u2, v2), rot, rect);
        let t_frac = i as f32 / max_visible as f32;
        let (color, width) = if is_covariant {
            let r = (200.0 * (1.0 - t_frac)) as u8;
            let g = (100.0 + 155.0 * t_frac) as u8;
            (egui::Color32::from_rgb(r, g, 50), 2.0)
        } else {
            let r = (200.0 + 55.0 * (1.0 - t_frac)) as u8;
            let g = (50.0 + 100.0 * t_frac) as u8;
            (egui::Color32::from_rgba_unmultiplied(r, g, 50, 160), 1.5)
        };
        painter.line_segment([sp1, sp2], egui::Stroke::new(width, color));
    }

    if max_visible > 0 {
        let start = &steps[0];
        let u = 2.0 * PI * start.position.x as f32;
        let v = 2.0 * PI * start.position.y as f32;
        let (sp, _) = project(torus_pt(rm, rn + 0.04, u, v), rot, rect);
        painter.circle_filled(sp, 4.0, egui::Color32::WHITE);
        let end = &steps[max_visible - 1];
        let u = 2.0 * PI * end.position.x as f32;
        let v = 2.0 * PI * end.position.y as f32;
        let (sp, _) = project(torus_pt(rm, rn + 0.04, u, v), rot, rect);
        let c = if is_covariant { FOREST_GREEN } else { WARN_RED };
        painter.circle_filled(sp, 4.0, c);
    }
}

// ─── Draw the CNT Doppler torus (with error arcs from snapshot) ─────────────

fn draw_cnt_torus(
    painter: &egui::Painter,
    rect: egui::Rect,
    rot: [f32; 2],
    grid_n: usize,
    snapshot: Option<&LatticeSnapshot>,
    time: f32,
) {
    let rm = 1.2_f32;
    let rn = 0.45_f32;
    let rings = 24_usize;
    let segs = 48_usize;

    // Surface patches
    for ring in 0..rings {
        let u0 = 2.0 * PI * ring as f32 / rings as f32;
        let u1 = 2.0 * PI * ((ring + 1) % rings) as f32 / rings as f32;
        for s in 0..segs {
            let v0 = 2.0 * PI * s as f32 / segs as f32;
            let v1 = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;
            let (p00, z00) = project(torus_pt(rm, rn, u0, v0), rot, rect);
            let (p10, z10) = project(torus_pt(rm, rn, u1, v0), rot, rect);
            let (p11, z11) = project(torus_pt(rm, rn, u1, v1), rot, rect);
            let (p01, z01) = project(torus_pt(rm, rn, u0, v1), rot, rect);
            let avg_z = (z00 + z10 + z11 + z01) * 0.25;
            let e1x = p10.x - p00.x;
            let e1y = p10.y - p00.y;
            let e2x = p01.x - p00.x;
            let e2y = p01.y - p00.y;
            if e1x * e2y - e1y * e2x > 0.0 {
                continue;
            }
            let depth_t = ((avg_z + 2.0) / 4.0).clamp(0.0, 1.0);
            let alpha = (18.0 + 22.0 * depth_t) as u8;
            let r = (20.0 + 50.0 * depth_t) as u8;
            let g = (60.0 + 80.0 * depth_t) as u8;
            let b = (50.0 + 30.0 * (1.0 - depth_t)) as u8;
            let mesh = egui::Mesh {
                indices: vec![0, 1, 2, 0, 2, 3],
                vertices: vec![
                    egui::epaint::Vertex { pos: p00, uv: egui::epaint::WHITE_UV, color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha) },
                    egui::epaint::Vertex { pos: p10, uv: egui::epaint::WHITE_UV, color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha) },
                    egui::epaint::Vertex { pos: p11, uv: egui::epaint::WHITE_UV, color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha) },
                    egui::epaint::Vertex { pos: p01, uv: egui::epaint::WHITE_UV, color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha) },
                ],
                texture_id: egui::TextureId::default(),
            };
            painter.add(egui::Shape::mesh(mesh));
        }
    }

    // Wireframe
    for ring in 0..rings {
        let fixed = 2.0 * PI * ring as f32 / rings as f32;
        for s in 0..segs {
            let a = 2.0 * PI * s as f32 / segs as f32;
            let b = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;
            for &(u_param, v_param) in &[(fixed, a), (a, fixed)] {
                let (s1, z1) = project(torus_pt(rm, rn, u_param, v_param), rot, rect);
                let v_b = if u_param == fixed { b } else { fixed };
                let u_b = if u_param == fixed { fixed } else { b };
                let (s2, z2) = project(torus_pt(rm, rn, u_b, v_b), rot, rect);
                let al = depth_alpha((z1 + z2) * 0.5);
                let dt = (((z1 + z2) * 0.5 + 2.0) / 4.0).clamp(0.0, 1.0);
                let wr = (TORUS_WIRE.r() as f32 * (0.6 + 0.4 * dt)) as u8;
                let wg = (TORUS_WIRE.g() as f32 * (0.6 + 0.4 * dt)) as u8;
                let wb = (TORUS_WIRE.b() as f32 * (0.6 + 0.4 * dt)) as u8;
                painter.line_segment([s1, s2], egui::Stroke::new(0.7, egui::Color32::from_rgba_unmultiplied(wr, wg, wb, al)));
            }
        }
    }

    // Non-contractible cycles
    for &(cycle_u, fixed_other) in &[(true, 0.0_f32), (true, PI), (false, 0.0), (false, PI)] {
        for s in 0..segs {
            let a = 2.0 * PI * s as f32 / segs as f32;
            let b = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;
            let (p1, p2) = if cycle_u {
                (torus_pt(rm, rn, fixed_other, a), torus_pt(rm, rn, fixed_other, b))
            } else {
                (torus_pt(rm, rn, a, fixed_other), torus_pt(rm, rn, b, fixed_other))
            };
            let (sc1, _) = project(p1, rot, rect);
            let (sc2, _) = project(p2, rot, rect);
            let pulse = 0.55 + 0.45 * (a + time * if cycle_u { -2.0 } else { 1.5 }).sin();
            let r = (212.0 * pulse + 80.0 * (1.0 - pulse)) as u8;
            let g = (175.0 * pulse + 100.0 * (1.0 - pulse)) as u8;
            let bl = (55.0 * pulse + 30.0 * (1.0 - pulse)) as u8;
            painter.line_segment([sc1, sc2], egui::Stroke::new(2.8, egui::Color32::from_rgb(r, g, bl)));
        }
    }

    // Qubit nodes
    for row in 0..grid_n {
        for col in 0..grid_n {
            let u = 2.0 * PI * row as f32 / grid_n as f32;
            let v = 2.0 * PI * col as f32 / grid_n as f32;
            let (sp, z) = project(torus_pt(rm, rn + 0.015, u, v), rot, rect);
            let al = depth_alpha(z);
            let ph = 0.6 + 0.4 * (time * 2.0 + u + v).sin();
            let br = (210.0 * ph) as u8;
            painter.circle_filled(sp, 2.5, egui::Color32::from_rgba_unmultiplied(br, br, (br as f32 * 0.9) as u8, al));
        }
    }

    // Error arcs on torus surface
    if let Some(snap) = snapshot {
        let n = snap.n;
        for row in 0..n {
            for col in 0..n {
                let h_idx = row * n + col;
                let hx = snap.x_errors.get(h_idx).copied().unwrap_or(false);
                let hz = snap.z_errors.get(h_idx).copied().unwrap_or(false);
                if hx || hz {
                    let c = error_color(hx, hz);
                    let u1 = 2.0 * PI * col as f32 / n as f32;
                    let u2 = 2.0 * PI * ((col + 1) % n) as f32 / n as f32;
                    let v = 2.0 * PI * row as f32 / n as f32;
                    let (a, _) = project(torus_pt(rm, rn + 0.04, u1, v), rot, rect);
                    let (b, _) = project(torus_pt(rm, rn + 0.04, u2, v), rot, rect);
                    painter.line_segment([a, b], egui::Stroke::new(2.5, c));
                }
                let v_idx = n * n + row * n + col;
                let vx = snap.x_errors.get(v_idx).copied().unwrap_or(false);
                let vz = snap.z_errors.get(v_idx).copied().unwrap_or(false);
                if vx || vz {
                    let c = error_color(vx, vz);
                    let u = 2.0 * PI * col as f32 / n as f32;
                    let v1 = 2.0 * PI * row as f32 / n as f32;
                    let v2 = 2.0 * PI * ((row + 1) % n) as f32 / n as f32;
                    let (a, _) = project(torus_pt(rm, rn + 0.04, u, v1), rot, rect);
                    let (b, _) = project(torus_pt(rm, rn + 0.04, u, v2), rot, rect);
                    painter.line_segment([a, b], egui::Stroke::new(2.5, c));
                }
            }
        }
    }
}

// ─── Draw the flat toric code lattice (CNT tab) ─────────────────────────────

fn draw_lattice(
    painter: &egui::Painter,
    rect: egui::Rect,
    snapshot: &LatticeSnapshot,
    hovered_node: Option<(usize, usize)>,
) {
    let n = snapshot.n;
    let m = 25.0_f32;
    let inner = egui::Rect::from_min_max(rect.min + egui::vec2(m, m + 14.0), rect.max - egui::vec2(m, m));
    let sx = inner.width() / n as f32;
    let sy = inner.height() / n as f32;

    // Syndrome count
    let e_count = snapshot.e_particles.len();
    let m_count = snapshot.m_particles.len();
    painter.text(
        rect.center_top() + egui::vec2(0.0, 28.0),
        egui::Align2::CENTER_TOP,
        format!("e-particles: {}  |  m-particles: {}", e_count, m_count),
        egui::FontId::monospace(10.0),
        DIM,
    );

    // Row/col labels
    for col in 0..n {
        let x = inner.left() + col as f32 * sx + sx * 0.5;
        painter.text(egui::pos2(x, inner.top() - 10.0), egui::Align2::CENTER_BOTTOM, format!("{}", col), egui::FontId::monospace(10.0), egui::Color32::from_rgb(100, 100, 95));
    }
    for row in 0..n {
        let y = inner.top() + row as f32 * sy + sy * 0.5;
        painter.text(egui::pos2(inner.left() - 10.0, y), egui::Align2::RIGHT_CENTER, format!("{}", row), egui::FontId::monospace(10.0), egui::Color32::from_rgb(100, 100, 95));
    }

    for row in 0..n {
        for col in 0..n {
            let x = inner.left() + col as f32 * sx + sx * 0.5;
            let y = inner.top() + row as f32 * sy + sy * 0.5;

            // Horizontal edge
            let hi = row * n + col;
            let hx = snapshot.x_errors.get(hi).copied().unwrap_or(false);
            let hz = snapshot.z_errors.get(hi).copied().unwrap_or(false);
            let x2 = if col + 1 < n { x + sx } else { inner.left() + sx * 0.5 };
            painter.line_segment([egui::pos2(x, y), egui::pos2(x2, y)], egui::Stroke::new(2.0, error_color(hx, hz)));

            // Vertical edge
            let vi = n * n + row * n + col;
            let vx = snapshot.x_errors.get(vi).copied().unwrap_or(false);
            let vz = snapshot.z_errors.get(vi).copied().unwrap_or(false);
            let y2 = if row + 1 < n { y + sy } else { inner.top() + sy * 0.5 };
            painter.line_segment([egui::pos2(x, y), egui::pos2(x, y2)], egui::Stroke::new(2.0, error_color(vx, vz)));

            // Hover highlight
            if hovered_node == Some((row, col)) {
                painter.circle_stroke(egui::pos2(x, y), 8.0, egui::Stroke::new(1.5, egui::Color32::WHITE));
            }

            // Vertex marker
            let is_e = snapshot.e_particles.contains(&(row, col));
            let (vc, vr) = if is_e { (E_PARTICLE_ORANGE, 5.0) } else { (egui::Color32::from_rgb(86, 166, 96), 3.0) };
            painter.circle_filled(egui::pos2(x, y), vr, vc);

            // Plaquette marker
            if snapshot.m_particles.contains(&(row, col)) {
                painter.rect_filled(
                    egui::Rect::from_center_size(egui::pos2(x + sx * 0.5, y + sy * 0.5), egui::vec2(7.0, 7.0)),
                    1.0,
                    WARN_RED,
                );
            }
        }
    }
}

fn lattice_vertex_pos(rect: egui::Rect, n: usize, row: usize, col: usize) -> egui::Pos2 {
    let m = 25.0_f32;
    let inner = egui::Rect::from_min_max(rect.min + egui::vec2(m, m + 14.0), rect.max - egui::vec2(m, m));
    let sx = inner.width() / n as f32;
    let sy = inner.height() / n as f32;
    egui::pos2(inner.left() + col as f32 * sx + sx * 0.5, inner.top() + row as f32 * sy + sy * 0.5)
}

fn hit_test_lattice(pos: egui::Pos2, rect: egui::Rect, n: usize) -> Option<(usize, usize)> {
    let threshold = 15.0_f32;
    let mut best: Option<(usize, usize)> = None;
    let mut best_dist = threshold;
    for row in 0..n {
        for col in 0..n {
            let vp = lattice_vertex_pos(rect, n, row, col);
            let d = vp.distance(pos);
            if d < best_dist {
                best_dist = d;
                best = Some((row, col));
            }
        }
    }
    best
}

// ═══════════════════════════════════════════════════════════════════════════════
//  App state
// ═══════════════════════════════════════════════════════════════════════════════

pub struct QuantumEngineApp {
    // Tab
    active_tab: Tab,

    // Engine config (sliders) — lengths in meters (log scale)
    l_max_m: f64,
    l_min_m: f64,
    temperature_k: f64,
    decoherence_rate: f64,
    modulation_depth_exp: f64,
    lattice_n: usize,
    // Descent params
    descent_eta: f64,
    descent_start_x: f64,
    descent_start_y: f64,
    show_euclidean: bool,
    // MC params
    #[allow(dead_code)]
    mc_trials: usize,
    #[allow(dead_code)]
    mc_error_rate: f64,
    // Engine results
    engine_result: Option<EngineResult>,
    descent_cov: Option<DescentResult>,
    descent_euc: Option<DescentResult>,
    scaling_data: Option<Vec<ScalingEntry>>,
    convergence_data: Option<Vec<(usize, f64, f64)>>,

    // CNT Doppler params
    cnt_params: PhysicsParams,
    cnt_lattice_n: usize,
    cnt_mc_trials: usize,
    cnt_gate_time_ns: f64,
    // CNT results
    cnt_physics_result: Option<PhysicsResult>,
    cnt_p_error: f64,
    cnt_logical_error_rate: f64,
    cnt_logical_failures: usize,
    cnt_mc_trials_done: usize,
    cnt_snapshot: Option<LatticeSnapshot>,
    cnt_chart_data: Option<ChartData>,
    cnt_hovered_node: Option<(usize, usize)>,

    // Hallucination reduction params
    drift_config: DriftConfig,
    drift_viz_mode: DriftVizMode,
    // Hallucination reduction results
    drift_result: Option<DriftResult>,
    drift_heatmap: Option<DriftHeatmap>,
    drift_analysis: Option<DriftAnalysisResult>,
    mask_analysis: Option<MaskAnalysisResult>,
    // Hallucination reduction worker flags
    needs_drift_mc: bool,
    needs_drift_heatmap: bool,
    needs_drift_analysis: bool,
    needs_mask_analysis: bool,

    // Visualization state (shared)
    time: f32,
    rotation: [f32; 2],
    auto_rotate: bool,
    paused: bool,
    // Worker
    worker: SimWorker,
    needs_engine: bool,
    needs_descent: bool,
    needs_scaling: bool,
    needs_convergence: bool,
    // CNT worker flags
    needs_cnt_eval: bool,
    needs_cnt_sweep: bool,
    cnt_sweep_pending: bool,
}

impl QuantumEngineApp {
    pub fn new(cc: &eframe::CreationContext<'_>) -> Self {
        cc.egui_ctx.set_visuals(forest_visuals());

        let mut style = (*cc.egui_ctx.style()).clone();
        style.text_styles.insert(egui::TextStyle::Heading, egui::FontId::proportional(17.0));
        style.text_styles.insert(egui::TextStyle::Body, egui::FontId::proportional(14.0));
        style.text_styles.insert(egui::TextStyle::Small, egui::FontId::proportional(12.0));
        style.text_styles.insert(egui::TextStyle::Monospace, egui::FontId::monospace(13.0));
        style.text_styles.insert(egui::TextStyle::Button, egui::FontId::proportional(14.0));
        cc.egui_ctx.set_style(style);

        let worker = SimWorker::spawn();

        let mut app = Self {
            active_tab: Tab::VacuumEngine,

            l_max_m: 3.0e-2,
            l_min_m: 2.9e-2,
            temperature_k: 0.020,
            decoherence_rate: 10.0,
            modulation_depth_exp: -5.0,
            lattice_n: 8,
            descent_eta: 0.002,
            descent_start_x: 0.95,
            descent_start_y: 0.05,
            show_euclidean: true,
            mc_trials: 5000,
            mc_error_rate: 0.03,
            engine_result: None,
            descent_cov: None,
            descent_euc: None,
            scaling_data: None,
            convergence_data: None,

            cnt_params: PhysicsParams::default(),
            cnt_lattice_n: 6,
            cnt_mc_trials: 500,
            cnt_gate_time_ns: cnt_bridge::DEFAULT_GATE_TIME_NS,
            cnt_physics_result: None,
            cnt_p_error: 0.0,
            cnt_logical_error_rate: 0.0,
            cnt_logical_failures: 0,
            cnt_mc_trials_done: 0,
            cnt_snapshot: None,
            cnt_chart_data: None,
            cnt_hovered_node: None,

            drift_config: DriftConfig::default(),
            drift_viz_mode: DriftVizMode::Overview,
            drift_result: None,
            drift_heatmap: None,
            drift_analysis: None,
            mask_analysis: None,
            needs_drift_mc: true,
            needs_drift_heatmap: true,
            needs_drift_analysis: true,
            needs_mask_analysis: true,

            time: 0.0,
            rotation: [0.3, 0.15],
            auto_rotate: true,
            paused: false,
            worker,
            needs_engine: true,
            needs_descent: true,
            needs_scaling: true,
            needs_convergence: true,
            needs_cnt_eval: false,
            needs_cnt_sweep: false,
            cnt_sweep_pending: false,
        };
        app.fire_all();
        app
    }

    fn build_config(&self) -> EngineConfig {
        EngineConfig {
            n: self.lattice_n,
            l_max: self.l_max_m,
            l_min: self.l_min_m,
            drive_frequency: 0.0,
            modulation_depth: (10.0_f64).powf(self.modulation_depth_exp),
            extraction_cycles: 1_000_000,
            decoherence_rate: self.decoherence_rate,
            temperature: self.temperature_k,
        }
    }

    fn apply_preset(&mut self, config: &EngineConfig) {
        self.l_max_m = config.l_max;
        self.l_min_m = config.l_min;
        self.temperature_k = config.temperature;
        self.decoherence_rate = config.decoherence_rate;
        self.modulation_depth_exp = config.modulation_depth.log10();
        self.lattice_n = config.n;
    }

    fn fire_all(&mut self) {
        self.send_engine();
        self.send_descent();
        self.send_scaling();
        self.send_convergence();
    }

    fn send_engine(&mut self) {
        self.worker.send(SimRequest::RunEngine { config: self.build_config() });
        self.needs_engine = false;
    }

    fn send_descent(&mut self) {
        let start = TorusPoint::new(self.descent_start_x, self.descent_start_y);
        let target = TorusPoint::new(0.05, 0.95);
        self.worker.send(SimRequest::RunDescent { n: self.lattice_n, eta: self.descent_eta, start, target });
        self.needs_descent = false;
    }

    fn send_scaling(&mut self) {
        self.worker.send(SimRequest::RunScaling { config: self.build_config(), sizes: vec![4, 6, 8, 10, 12, 16, 24] });
        self.needs_scaling = false;
    }

    fn send_convergence(&mut self) {
        self.worker.send(SimRequest::RunConvergence { sizes: vec![4, 6, 8, 12, 16, 24], eta: 0.001 });
        self.needs_convergence = false;
    }

    fn send_cnt_eval(&mut self) {
        self.worker.send(SimRequest::RunCntEval {
            params: self.cnt_params.clone(),
            lattice_n: self.cnt_lattice_n,
            gate_time_ns: self.cnt_gate_time_ns,
            mc_trials: self.cnt_mc_trials,
        });
        self.needs_cnt_eval = false;
    }

    fn send_cnt_sweep(&mut self) {
        self.worker.send(SimRequest::RunCntSweep {
            lattice_n: self.cnt_lattice_n,
            mc_trials: (self.cnt_mc_trials / 5).max(50),
            operating_p: self.cnt_p_error,
        });
        self.needs_cnt_sweep = false;
        self.cnt_sweep_pending = true;
    }

    fn send_drift_mc(&mut self) {
        self.worker.send(SimRequest::RunDriftMC { config: self.drift_config.clone() });
        self.needs_drift_mc = false;
    }

    fn send_drift_heatmap(&mut self) {
        let center = self.drift_config.grid_n / 2;
        self.worker.send(SimRequest::RunMaskHeatmap {
            config: self.drift_config.clone(),
            ref_pos: (center, center),
        });
        self.needs_drift_heatmap = false;
    }

    fn send_drift_analysis(&mut self) {
        self.worker.send(SimRequest::RunDriftAnalysis {
            config: self.drift_config.clone(),
        });
        self.needs_drift_analysis = false;
    }

    fn send_mask_analysis(&mut self) {
        self.worker.send(SimRequest::RunMaskAnalysis {
            config: self.drift_config.clone(),
        });
        self.needs_mask_analysis = false;
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Frame update
// ═══════════════════════════════════════════════════════════════════════════════

impl eframe::App for QuantumEngineApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        if ctx.input(|i| i.key_pressed(egui::Key::Space)) {
            self.paused = !self.paused;
        }

        let dt = ctx.input(|i| i.stable_dt).min(0.05);
        if !self.paused {
            self.time += dt;
            if self.auto_rotate {
                self.rotation[0] += dt * 0.10;
                self.rotation[1] += dt * 0.05;
            }
        }

        // Poll worker — handle all response types
        while let Some(resp) = self.worker.try_recv() {
            match resp {
                SimResponse::Engine(result) => {
                    self.engine_result = Some(result);
                }
                SimResponse::Descent { euclidean, covariant } => {
                    self.descent_euc = Some(euclidean);
                    self.descent_cov = Some(covariant);
                }
                SimResponse::Scaling(entries) => {
                    self.scaling_data = Some(entries);
                }
                SimResponse::Convergence(data) => {
                    self.convergence_data = Some(data);
                }
                SimResponse::CntEvaluated { physics, p_error, mc_result, snapshot } => {
                    self.cnt_p_error = p_error;
                    self.cnt_logical_error_rate = mc_result.logical_error_rate;
                    self.cnt_logical_failures = mc_result.logical_failures;
                    self.cnt_mc_trials_done = mc_result.trials;
                    self.cnt_physics_result = Some(physics);
                    self.cnt_snapshot = Some(snapshot);
                    if !self.cnt_sweep_pending { self.needs_cnt_sweep = true; }
                }
                SimResponse::CntSweptChart(chart) => {
                    self.cnt_chart_data = Some(chart);
                    self.cnt_sweep_pending = false;
                }
                SimResponse::DriftMC(result) => {
                    self.drift_result = Some(result);
                }
                SimResponse::MaskHeatmap(heatmap) => {
                    self.drift_heatmap = Some(heatmap);
                }
                SimResponse::DriftAnalysis(result) => {
                    self.drift_analysis = Some(result);
                }
                SimResponse::MaskAnalysis(result) => {
                    self.mask_analysis = Some(result);
                }
            }
        }

        // Fire drift simulations when needed and tab is active
        if self.active_tab == Tab::HallucinationReduction {
            if self.needs_drift_mc { self.send_drift_mc(); }
            if self.needs_drift_heatmap { self.send_drift_heatmap(); }
            if self.needs_drift_analysis && self.drift_viz_mode == DriftVizMode::DriftAnalysis {
                self.send_drift_analysis();
            }
            if self.needs_mask_analysis && self.drift_viz_mode == DriftVizMode::MaskAnalysis {
                self.send_mask_analysis();
            }
        }

        // ═════ LEFT PANEL: Controls (conditional on tab) ═════
        egui::SidePanel::left("controls")
            .min_width(240.0)
            .max_width(300.0)
            .show(ctx, |ui| {
                egui::ScrollArea::vertical().show(ui, |ui| {
                    ui.add_space(4.0);

                    // Branding
                    ui.horizontal(|ui| {
                        ui.colored_label(GOLD_EG, egui::RichText::new("PARAXIOM").strong().size(14.0));
                        ui.colored_label(DIM, egui::RichText::new("Technologies").size(12.0));
                    });
                    ui.add_space(2.0);

                    // Tab bar
                    ui.horizontal(|ui| {
                        ui.selectable_value(&mut self.active_tab, Tab::VacuumEngine, egui::RichText::new("Vacuum Engine").strong());
                        ui.selectable_value(&mut self.active_tab, Tab::CntDoppler, egui::RichText::new("CNT Doppler").strong());
                        ui.selectable_value(&mut self.active_tab, Tab::HallucinationReduction, egui::RichText::new("Hallucination").strong());
                    });
                    ui.separator();

                    // Pause/Resume
                    ui.horizontal(|ui| {
                        let (label, color) = if self.paused { ("RESUME", FOREST_GREEN) } else { ("PAUSE", GOLD_EG) };
                        if ui.add(egui::Button::new(egui::RichText::new(label).strong().color(color))).clicked() {
                            self.paused = !self.paused;
                        }
                        ui.colored_label(egui::Color32::from_rgb(110, 110, 105), egui::RichText::new("(or Space)").size(11.0));
                    });
                    ui.add_space(4.0);

                    match self.active_tab {
                        Tab::VacuumEngine => self.draw_engine_controls(ui),
                        Tab::CntDoppler => self.draw_cnt_controls(ui),
                        Tab::HallucinationReduction => self.draw_drift_controls(ui),
                    }
                });
            });

        // ═════ RIGHT PANEL: Results (conditional on tab) ═════
        egui::SidePanel::right("results")
            .min_width(220.0)
            .max_width(280.0)
            .show(ctx, |ui| {
                egui::ScrollArea::vertical().show(ui, |ui| {
                    match self.active_tab {
                        Tab::VacuumEngine => self.draw_engine_results(ui),
                        Tab::CntDoppler => self.draw_cnt_results(ui),
                        Tab::HallucinationReduction => self.draw_drift_results(ui),
                    }
                });
            });

        // ═════ CENTRAL PANEL: Visualizations (conditional on tab) ═════
        egui::CentralPanel::default()
            .frame(egui::Frame::NONE.fill(egui::Color32::from_rgb(20, 24, 20)))
            .show(ctx, |ui| {
                match self.active_tab {
                    Tab::VacuumEngine => self.draw_engine_central(ui),
                    Tab::CntDoppler => self.draw_cnt_central(ui, ctx),
                    Tab::HallucinationReduction => self.draw_drift_central(ui),
                }
            });

        // Status badge (conditional on tab)
        match self.active_tab {
            Tab::VacuumEngine => self.draw_engine_status(ctx),
            Tab::CntDoppler => self.draw_cnt_status(ctx),
            Tab::HallucinationReduction => self.draw_drift_status(ctx),
        }

        ctx.request_repaint();
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Vacuum Engine tab methods
// ═══════════════════════════════════════════════════════════════════════════════

impl QuantumEngineApp {
    fn draw_engine_controls(&mut self, ui: &mut egui::Ui) {
        ui.colored_label(GOLD_EG, egui::RichText::new("QUANTUM ENGINE VISUALIZER").strong().size(13.0));
        dim_label(ui, "Toroidal vacuum engine on T\u{00b2}");
        ui.add_space(4.0);

        // Presets
        section_heading(ui, "PRESETS");
        let mut preset_clicked = false;
        ui.horizontal(|ui| {
            if ui.add(egui::Button::new(egui::RichText::new("Microwave").color(COMPRESS_BLUE).size(12.0))).clicked() {
                self.apply_preset(&EngineConfig::microwave());
                preset_clicked = true;
            }
            if ui.add(egui::Button::new(egui::RichText::new("Mid-IR").color(THERMAL_ORANGE).size(12.0))).clicked() {
                self.apply_preset(&EngineConfig::mid_infrared());
                preset_clicked = true;
            }
            if ui.add(egui::Button::new(egui::RichText::new("Optical").color(EXTRACT_GOLD).size(12.0))).clicked() {
                self.apply_preset(&EngineConfig::optical());
                preset_clicked = true;
            }
        });

        // Cavity Parameters
        section_heading(ui, "CAVITY PARAMETERS");
        let mut engine_changed = preset_clicked;
        let freq_regime = if self.l_min_m > 1e-3 { "Microwave" } else if self.l_min_m > 1e-5 { "Mid-infrared" } else { "Optical" };
        dim_label(ui, &format!("Regime: {}", freq_regime));

        ui.add_space(4.0);
        ui.label("L_max (m)");
        dim_label(ui, &format!("Expanded cavity. {}", format_length(self.l_max_m)));
        engine_changed |= ui.add(egui::Slider::new(&mut self.l_max_m, 1e-6..=0.1).logarithmic(true)).changed();

        ui.add_space(2.0);
        ui.label("L_min (m)");
        dim_label(ui, &format!("Compressed cavity. {}", format_length(self.l_min_m)));
        engine_changed |= ui.add(egui::Slider::new(&mut self.l_min_m, 1e-6..=0.1).logarithmic(true)).changed();

        if self.l_min_m >= self.l_max_m {
            self.l_min_m = self.l_max_m * 0.98;
        }

        ui.add_space(2.0);
        ui.label("Temperature (K)");
        dim_label(ui, "Operating temperature.");
        engine_changed |= ui.add(egui::Slider::new(&mut self.temperature_k, 0.001..=300.0).logarithmic(true)).changed();

        ui.add_space(2.0);
        ui.label("\u{03b3} (Hz)");
        dim_label(ui, "Decoherence rate = \u{03c9}/Q.");
        engine_changed |= ui.add(egui::Slider::new(&mut self.decoherence_rate, 0.1..=1e9).logarithmic(true)).changed();

        ui.add_space(2.0);
        ui.label("\u{03b4}L/L (10^x)");
        dim_label(ui, "Modulation depth for DCE.");
        engine_changed |= ui.add(egui::Slider::new(&mut self.modulation_depth_exp, -8.0..=-2.0).step_by(0.5)).changed();

        // Lattice
        section_heading(ui, "LATTICE");
        ui.add_space(4.0);
        ui.label("N (lattice dimension)");
        dim_label(ui, "N\u{00d7}N torus.");
        let lattice_changed = ui.add(egui::Slider::new(&mut self.lattice_n, 4..=32)).changed();
        engine_changed |= lattice_changed;

        // Covariant Descent
        section_heading(ui, "COVARIANT DESCENT");
        dim_label(ui, "Gradient descent on T\u{00b2} surface.");
        let mut descent_changed = false;
        ui.add_space(4.0);
        ui.label("Learning rate \u{03b7}");
        descent_changed |= ui.add(egui::Slider::new(&mut self.descent_eta, 0.0001..=0.05).logarithmic(true)).changed();
        ui.add_space(2.0);
        ui.label("Start x");
        descent_changed |= ui.add(egui::Slider::new(&mut self.descent_start_x, 0.0..=1.0)).changed();
        ui.add_space(2.0);
        ui.label("Start y");
        descent_changed |= ui.add(egui::Slider::new(&mut self.descent_start_y, 0.0..=1.0)).changed();
        ui.add_space(2.0);
        ui.checkbox(&mut self.show_euclidean, "Show Euclidean path");
        descent_changed |= lattice_changed;

        if engine_changed { self.needs_engine = true; self.needs_scaling = true; }
        if descent_changed { self.needs_descent = true; }
        if lattice_changed { self.needs_convergence = true; }

        if self.needs_engine { self.send_engine(); }
        if self.needs_descent { self.send_descent(); }
        if self.needs_scaling { self.send_scaling(); }
        if self.needs_convergence { self.send_convergence(); }

        ui.add_space(6.0);
        ui.separator();
        dim_label(ui, "ENGINE CYCLE:");
        dim_label(ui, "  1. Compress (L_max\u{2192}L_min)");
        dim_label(ui, "  2. Extract (DCE photons)");
        dim_label(ui, "  3. Expand (release work)");
        dim_label(ui, "  4. Idle (re-thermalize)");
    }

    fn draw_engine_results(&self, ui: &mut egui::Ui) {
        section_heading(ui, "ENGINE RESULTS");

        if let Some(ref r) = self.engine_result {
            let config = &r.config;
            let omega_1 = 2.0 * std::f64::consts::PI * crate::units::C / config.l_min;
            let q_factor = omega_1 / config.decoherence_rate;

            ui.label(format!("\u{03c9}\u{2081} = {}", format_freq(omega_1)));
            dim_label(ui, "  Fundamental mode");
            ui.label(format!("Q = {:.1e}", q_factor));
            dim_label(ui, "  Quality factor");
            ui.label(format!("n_th = {:.2e}", r.thermal_photons));
            dim_label(ui, "  Thermal photons");
            ui.label(format!("\u{03b4}L\u{00b7}\u{03c9}/c = {:.2e}", r.perturbative_param));

            let pert_color = if r.perturbative_param < 0.01 { FOREST_GREEN } else { WARN_RED };
            let pert_label = if r.perturbative_param < 0.01 { "PERTURBATIVE" } else { "NON-PERTURBATIVE" };
            ui.colored_label(pert_color, egui::RichText::new(pert_label).strong());

            ui.add_space(6.0);
            section_heading(ui, "SPECTRAL GAP");
            ui.label(format!("\u{03bb}\u{2081} = {:.6}", r.cycle.spectral_gap));
            dim_label(ui, "  Controls all coherence bounds");
            ui.label(format!("Protection: {:.2e}", r.cycle.protection_factor));
            dim_label(ui, "  exp(-\u{03bb}\u{2081}/\u{03b3}_norm)");

            ui.add_space(6.0);
            section_heading(ui, "ENGINE CYCLE");
            ui.label(format!("W_compress: {:.3e} J", r.cycle.work_compression));
            ui.label(format!("E_extract:  {:.3e} J", r.cycle.energy_extracted));
            ui.label(format!("Loss:       {:.3e} J", r.cycle.decoherence_loss));
            ui.label(format!("Thermal:    {:.3e} J", r.cycle.thermal_noise));
            ui.separator();
            let net_color = if r.cycle.net_work > 0.0 { FOREST_GREEN } else { WARN_RED };
            ui.colored_label(net_color, format!("Net work:   {:.3e} J", r.cycle.net_work));
            ui.label(format!("Power:      {:.3e} W", r.power_output));

            ui.add_space(6.0);
            section_heading(ui, "EFFICIENCY");
            ui.label(format!("\u{03b7} = {:.4e}", r.cycle.efficiency));
            dim_label(ui, "  With topological protection");
            ui.label(format!("\u{03b7}\u{2080} = {:.4e}", r.efficiency_unprotected));
            dim_label(ui, "  Without protection");
            if r.cycle.efficiency != 0.0 && r.efficiency_unprotected != 0.0 {
                let ratio = r.cycle.efficiency / r.efficiency_unprotected;
                let rc = if ratio > 1.0 { FOREST_GREEN } else { WARN_RED };
                ui.colored_label(rc, format!("\u{03b7}/\u{03b7}\u{2080} = {:.2}\u{00d7}", ratio));
            }

            ui.add_space(6.0);
            section_heading(ui, "COHERENCE");
            let ec = if r.coherence_enhancement > 1.0 { FOREST_GREEN } else { GOLD_EG };
            ui.colored_label(ec, format!("Enhancement: {:.2}\u{00d7}", r.coherence_enhancement));
            dim_label(ui, "  Tonnetz vs bare T\u{2082}");
            ui.label(format!("Unruh a_min: {:.2e} m/s\u{00b2}", r.unruh_acceleration_threshold));
        } else {
            dim_label(ui, "Computing...");
        }

        // Descent results
        ui.add_space(6.0);
        section_heading(ui, "DESCENT COMPARISON");
        if let Some(ref cov) = self.descent_cov {
            let conv_str = match cov.convergence_step { Some(s) => format!("step {}", s), None => "not converged".to_string() };
            ui.colored_label(FOREST_GREEN, "Covariant (T\u{00b2}):");
            ui.label(format!("  Loss: {:.6}", cov.final_loss));
            ui.label(format!("  Conv: {}", conv_str));
            ui.label(format!("  Rate: {:.6}", cov.measured_rate));
        }
        if let Some(ref euc) = self.descent_euc {
            let conv_str = match euc.convergence_step { Some(s) => format!("step {}", s), None => "not converged".to_string() };
            ui.colored_label(WARN_RED, "Euclidean (flat):");
            ui.label(format!("  Loss: {:.6}", euc.final_loss));
            ui.label(format!("  Conv: {}", conv_str));
            ui.label(format!("  Rate: {:.6}", euc.measured_rate));
        }
    }

    fn draw_engine_central(&self, ui: &mut egui::Ui) {
        let full = ui.available_rect_before_wrap();
        let torus_h = (full.height() * 0.55).max(200.0);
        let torus_rect = egui::Rect::from_min_max(full.min, egui::pos2(full.max.x, full.min.y + torus_h));
        let chart_area = egui::Rect::from_min_max(egui::pos2(full.min.x, full.min.y + torus_h), full.max);
        let col_w = chart_area.width() / 3.0;
        let chart1 = egui::Rect::from_min_max(chart_area.min, egui::pos2(chart_area.min.x + col_w, chart_area.max.y));
        let chart2 = egui::Rect::from_min_max(egui::pos2(chart_area.min.x + col_w, chart_area.min.y), egui::pos2(chart_area.min.x + 2.0 * col_w, chart_area.max.y));
        let chart3 = egui::Rect::from_min_max(egui::pos2(chart_area.min.x + 2.0 * col_w, chart_area.min.y), chart_area.max);

        let torus_response = ui.allocate_rect(torus_rect, egui::Sense::click_and_drag());
        if torus_response.dragged() {
            // rotation is handled via interior mutability workaround — but since &self, we skip drag here
            // (drag is handled in the main update for the torus_rect area)
        }

        {
            let painter = ui.painter();
            let (phase, _) = cycle_phase(self.time);
            let phase_name = match phase { CyclePhase::Compress => "COMPRESS", CyclePhase::Extract => "EXTRACT", CyclePhase::Expand => "EXPAND", CyclePhase::Idle => "IDLE" };
            let phase_col = match phase { CyclePhase::Compress => COMPRESS_BLUE, CyclePhase::Extract => EXTRACT_GOLD, CyclePhase::Expand => EXPAND_GREEN, CyclePhase::Idle => DIM };
            painter.text(torus_rect.center_top() + egui::vec2(0.0, 12.0), egui::Align2::CENTER_TOP, format!("3D TORUS (T\u{00b2}) \u{2014} {0}\u{00d7}{0} lattice", self.lattice_n), egui::FontId::proportional(13.0), HEADING_CLR);
            painter.text(torus_rect.center_top() + egui::vec2(0.0, 28.0), egui::Align2::CENTER_TOP, format!("Engine phase: {}", phase_name), egui::FontId::proportional(11.0), phase_col);

            let cov_steps = self.descent_cov.as_ref().map(|d| d.steps.as_slice());
            let euc_steps = self.descent_euc.as_ref().map(|d| d.steps.as_slice());
            draw_engine_torus(painter, torus_rect, self.rotation, self.lattice_n, self.time, cov_steps, euc_steps, self.show_euclidean);

            painter.text(chart1.center_top() + egui::vec2(0.0, 4.0), egui::Align2::CENTER_TOP, "ENGINE CYCLE ENERGY", egui::FontId::proportional(11.0), HEADING_CLR);
            painter.text(chart2.center_top() + egui::vec2(0.0, 4.0), egui::Align2::CENTER_TOP, "CONVERGENCE RATE vs \u{03bb}\u{2081}", egui::FontId::proportional(11.0), HEADING_CLR);
            painter.text(chart3.center_top() + egui::vec2(0.0, 4.0), egui::Align2::CENTER_TOP, "SCALING: \u{03b7}, DCE, Enhancement vs N", egui::FontId::proportional(11.0), HEADING_CLR);
        }

        // Chart 1: Energy Budget
        let chart1_inner = egui::Rect::from_min_max(chart1.min + egui::vec2(8.0, 20.0), chart1.max - egui::vec2(8.0, 5.0));
        ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart1_inner), |ui| {
            Plot::new("energy_budget").width(chart1_inner.width()).height(chart1_inner.height()).y_axis_label("Energy (J)").show_axes(true).allow_zoom(true).allow_drag(true).legend(Legend::default().position(Corner::RightTop)).show(ui, |plot_ui| {
                if let Some(ref r) = self.engine_result {
                    let bars = vec![
                        Bar::new(0.0, r.cycle.work_compression).name("W_compress").fill(COMPRESS_BLUE),
                        Bar::new(1.0, r.cycle.energy_extracted).name("E_extract").fill(EXTRACT_GOLD),
                        Bar::new(2.0, r.cycle.decoherence_loss).name("Decoherence").fill(LOSS_RED),
                        Bar::new(3.0, r.cycle.thermal_noise).name("Thermal").fill(THERMAL_ORANGE),
                        Bar::new(4.0, r.cycle.net_work.max(0.0)).name("Net work").fill(FOREST_GREEN),
                    ];
                    plot_ui.bar_chart(BarChart::new(bars).width(0.7));
                }
            });
        });

        // Chart 2: Convergence Rate vs λ₁
        let chart2_inner = egui::Rect::from_min_max(chart2.min + egui::vec2(8.0, 20.0), chart2.max - egui::vec2(8.0, 5.0));
        ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart2_inner), |ui| {
            Plot::new("convergence_chart").width(chart2_inner.width()).height(chart2_inner.height()).x_axis_label("\u{03bb}\u{2081}").y_axis_label("Measured rate").show_axes(true).allow_zoom(true).allow_drag(true).legend(Legend::default().position(Corner::LeftTop)).show(ui, |plot_ui| {
                if let Some(ref data) = self.convergence_data {
                    let pts: PlotPoints = data.iter().map(|&(_, l, m)| [l, m]).collect();
                    plot_ui.points(Points::new(pts).color(FOREST_GREEN).radius(5.0).name("rate vs \u{03bb}\u{2081}"));
                    for &(n, l, m) in data {
                        plot_ui.text(PlotText::new(PlotPoint::new(l, m), egui::RichText::new(format!("N={}", n)).size(9.0).color(DIM)).anchor(egui::Align2::LEFT_BOTTOM));
                    }
                    if let Some(&(_, l0, m0)) = data.first() {
                        if l0 > 0.0 {
                            let k = m0 / l0;
                            let max_l = data.iter().map(|&(_, l, _)| l).fold(0.0_f64, f64::max);
                            plot_ui.line(Line::new(PlotPoints::from(vec![[0.0, 0.0], [max_l, k * max_l]])).color(GOLD_EG).width(1.5).name("rate \u{221d} \u{03bb}\u{2081}"));
                        }
                    }
                }
            });
        });

        // Chart 3: Scaling Study
        let chart3_inner = egui::Rect::from_min_max(chart3.min + egui::vec2(8.0, 20.0), chart3.max - egui::vec2(8.0, 5.0));
        ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart3_inner), |ui| {
            Plot::new("scaling_chart").width(chart3_inner.width()).height(chart3_inner.height()).x_axis_label("N").show_axes(true).allow_zoom(true).allow_drag(true).legend(Legend::default().position(Corner::LeftTop)).show(ui, |plot_ui| {
                if let Some(ref data) = self.scaling_data {
                    let enh_line: PlotPoints = data.iter().map(|e| [e.n as f64, e.coherence_enhancement]).collect();
                    let enh_scatter: PlotPoints = data.iter().map(|e| [e.n as f64, e.coherence_enhancement]).collect();
                    plot_ui.line(Line::new(enh_line).color(FOREST_GREEN).width(2.0).name("Enhancement (\u{00d7})"));
                    plot_ui.points(Points::new(enh_scatter).color(FOREST_GREEN).radius(4.0).name("Enhancement"));
                    let max_dce = data.iter().map(|e| e.dce_pair_rate).fold(0.0_f64, f64::max);
                    if max_dce > 0.0 {
                        let dce_pts: PlotPoints = data.iter().map(|e| [e.n as f64, e.dce_pair_rate / max_dce * data.iter().map(|x| x.coherence_enhancement).fold(0.0_f64, f64::max)]).collect();
                        plot_ui.line(Line::new(dce_pts).color(GOLD_EG).width(2.0).name("DCE (normalized)"));
                    }
                    let max_gap = data.iter().map(|e| e.spectral_gap).fold(0.0_f64, f64::max);
                    let max_enh = data.iter().map(|e| e.coherence_enhancement).fold(0.0_f64, f64::max);
                    if max_gap > 0.0 {
                        let gap_pts: PlotPoints = data.iter().map(|e| [e.n as f64, e.spectral_gap / max_gap * max_enh]).collect();
                        plot_ui.line(Line::new(gap_pts).color(egui::Color32::from_rgb(200, 200, 190)).width(1.5).name("\u{03bb}\u{2081} (scaled)"));
                    }
                }
            });
        });
    }

    fn draw_engine_status(&self, ctx: &egui::Context) {
        if let Some(ref r) = self.engine_result {
            let (st, sc) = if r.perturbative_param < 0.01 { ("PERTURBATIVE", FOREST_GREEN) } else { ("NON-PERTURBATIVE", WARN_RED) };
            let frame = egui::Frame {
                fill: egui::Color32::from_rgba_unmultiplied(22, 28, 22, 230),
                corner_radius: egui::CornerRadius::from(6),
                inner_margin: egui::Margin::same(10),
                stroke: egui::Stroke::new(2.0, sc),
                ..Default::default()
            };
            egui::Window::new("status").title_bar(false).resizable(false).movable(false).frame(frame).anchor(egui::Align2::RIGHT_BOTTOM, [-10.0, -10.0]).show(ctx, |ui| {
                ui.colored_label(sc, egui::RichText::new(st).strong().size(15.0));
                ui.label(format!("\u{03b7}={:.2e}  \u{03bb}\u{2081}={:.4}  enhance={:.1}\u{00d7}", r.cycle.efficiency, r.cycle.spectral_gap, r.coherence_enhancement));
                dim_label(ui, &format!("P={:.2e}W  n_th={:.1e}", r.power_output, r.thermal_photons));
                if self.paused { ui.colored_label(GOLD_EG, egui::RichText::new("PAUSED").size(11.0)); }
            });
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  CNT Doppler tab methods
// ═══════════════════════════════════════════════════════════════════════════════

impl QuantumEngineApp {
    fn draw_cnt_controls(&mut self, ui: &mut egui::Ui) {
        ui.colored_label(GOLD_EG, egui::RichText::new("DOPPLER-TORIC SIMULATOR").strong().size(13.0));
        dim_label(ui, "Physical layer \u{2192} logical layer bridge");
        ui.add_space(4.0);

        section_heading(ui, "PHYSICAL LAYER: Doppler Cooling");
        dim_label(ui, "CNT optomechanical resonator cooled by laser.");
        let mut changed = false;

        ui.add_space(4.0);
        ui.label("Temperature (K)");
        dim_label(ui, "Bath temperature. Lower = fewer thermal phonons.");
        changed |= ui.add(egui::Slider::new(&mut self.cnt_params.temperature, 0.01..=300.0).logarithmic(true)).changed();

        ui.add_space(2.0);
        ui.label("Laser Power (mW)");
        dim_label(ui, "Drives intracavity photon number \u{2192} cooperativity.");
        changed |= ui.add(egui::Slider::new(&mut self.cnt_params.laser_power, 0.1..=50.0).logarithmic(true)).changed();

        ui.add_space(2.0);
        ui.label("Detuning (\u{00d7}\u{03c9}_m)");
        dim_label(ui, "Red detuning (-1 = optimal sideband cooling).");
        changed |= ui.add(egui::Slider::new(&mut self.cnt_params.detuning, -3.0..=0.0)).changed();

        ui.add_space(2.0);
        ui.label("\u{03ba}/2 (\u{00d7}\u{03c9}_m)");
        dim_label(ui, "Cavity half-linewidth.");
        changed |= ui.add(egui::Slider::new(&mut self.cnt_params.kappa, 0.01..=2.0).logarithmic(true)).changed();

        ui.add_space(2.0);
        ui.label("Piezo Voltage (V)");
        dim_label(ui, "Piezoelectric drive near mechanical resonance.");
        changed |= ui.add(egui::Slider::new(&mut self.cnt_params.piezo_voltage, 0.0..=10.0)).changed();

        section_heading(ui, "TONNETZ COHERENCE FILTER");
        dim_label(ui, "Toroidal topology suppresses dephasing noise.");
        ui.add_space(4.0);
        ui.label("Grid Size (N)");
        dim_label(ui, "N\u{00d7}N Tonnetz torus. Larger \u{2192} stronger suppression.");
        changed |= ui.add(egui::Slider::new(&mut self.cnt_params.tonnetz_grid_size, 3..=16)).changed();
        ui.add_space(2.0);
        ui.label("Q Factor");
        dim_label(ui, "Quality factor. Higher = more enhancement.");
        changed |= ui.add(egui::Slider::new(&mut self.cnt_params.tonnetz_q, 1.0..=200.0).logarithmic(true)).changed();

        section_heading(ui, "LOGICAL LAYER: Toric Code");
        dim_label(ui, "Kitaev toric code + greedy decoder.");
        ui.add_space(4.0);
        ui.label("Lattice N");
        dim_label(ui, "N\u{00d7}N torus with 2N\u{00b2} physical qubits.");
        changed |= ui.add(egui::Slider::new(&mut self.cnt_lattice_n, 3..=12)).changed();
        ui.add_space(2.0);
        ui.label("MC Trials");
        dim_label(ui, "Monte Carlo error-correction trials.");
        changed |= ui.add(egui::Slider::new(&mut self.cnt_mc_trials, 50..=5000).logarithmic(true)).changed();
        ui.add_space(2.0);
        ui.label("Gate Time (ns)");
        dim_label(ui, "p = gate_time / T\u{2082}");
        changed |= ui.add(egui::Slider::new(&mut self.cnt_gate_time_ns, 10.0..=1000.0).logarithmic(true)).changed();

        if changed {
            self.needs_cnt_eval = true;
            self.needs_cnt_sweep = true;
        }
        if self.needs_cnt_eval { self.send_cnt_eval(); }
        if self.needs_cnt_sweep && !self.cnt_sweep_pending { self.send_cnt_sweep(); }

        ui.add_space(6.0);
        ui.separator();
        dim_label(ui, "PIPELINE:");
        dim_label(ui, "  Temp,Laser \u{2192} Doppler \u{2192} n_final");
        dim_label(ui, "  Tonnetz(\u{03bb}\u{2081},Q) \u{2192} T\u{2082} enhancement");
        dim_label(ui, "  T\u{2082} \u{2192} p = t_gate/T\u{2082}");
        dim_label(ui, "  p \u{2192} Toric code MC \u{2192} P_L");
    }

    fn draw_cnt_results(&self, ui: &mut egui::Ui) {
        section_heading(ui, "PHYSICS RESULTS");

        if let Some(ref phys) = self.cnt_physics_result {
            ui.label(format!("n_th: {:.1}", phys.n_thermal));
            dim_label(ui, "  Thermal phonon number");
            ui.label(format!("C: {:.1}", phys.cooperativity));
            dim_label(ui, "  Cooperativity");
            ui.label(format!("n_f: {:.4}", phys.n_final));
            dim_label(ui, "  Final phonon occupation");

            ui.add_space(6.0);
            section_heading(ui, "TONNETZ FILTER");
            ui.label(format!("\u{03bb}\u{2081}: {:.4}", phys.spectral_gap));
            dim_label(ui, "  Spectral gap");
            ui.label(format!("\u{03a3}w: {:.1}", phys.coupling_weight));
            dim_label(ui, "  Total coupling weight");
            let enh_c = if phys.tonnetz_enhancement > 5.0 { FOREST_GREEN } else { GOLD_EG };
            ui.colored_label(enh_c, format!("Enhancement: {:.1}\u{00d7}", phys.tonnetz_enhancement));
            dim_label(ui, "  Dephasing suppression factor");

            ui.add_space(6.0);
            section_heading(ui, "COHERENCE TIMES");
            ui.label(format!("T\u{2081}: {:.0} ns", phys.t1_ns));
            dim_label(ui, "  Relaxation time");
            let t2c = if phys.t2_ns > self.cnt_gate_time_ns * 10.0 { FOREST_GREEN } else { WARN_RED };
            ui.colored_label(t2c, format!("T\u{2082}: {:.0} ns  (with Tonnetz)", phys.t2_ns));
            dim_label(ui, "  Phase coherence time");
            ui.label(format!("T\u{2082} bare: {:.0} ns", phys.t2_bare_ns));
            let imp = phys.t2_ns - phys.t2_bare_ns;
            let imp_c = if imp > 100.0 { FOREST_GREEN } else { GOLD_EG };
            ui.colored_label(imp_c, format!("\u{0394}T\u{2082}: +{:.0} ns improvement", imp));
        }

        ui.add_space(6.0);
        section_heading(ui, "ERROR CORRECTION");
        ui.label(format!("p = {:.4}", self.cnt_p_error));
        dim_label(ui, "  Physical error rate");
        let margin = 0.09 - self.cnt_p_error;
        let mc = if margin > 0.0 { FOREST_GREEN } else { WARN_RED };
        ui.colored_label(mc, format!("Margin: {:.1}%", margin * 100.0));
        if margin > 0.0 { dim_label(ui, "  BELOW threshold \u{2713}"); } else { ui.colored_label(WARN_RED, "  ABOVE threshold!"); }
        ui.label(format!("P_L = {:.3}  ({}/{})", self.cnt_logical_error_rate, self.cnt_logical_failures, self.cnt_mc_trials_done));
        dim_label(ui, "  Logical error rate");

        ui.add_space(8.0);
        ui.separator();
        dim_label(ui, "COLOR KEY:");
        ui.colored_label(X_ERROR_RED, "  Red = X errors (bit flips)");
        ui.colored_label(Z_ERROR_BLUE, "  Blue = Z errors (phase flips)");
        ui.colored_label(Y_ERROR_PURPLE, "  Purple = Y errors (both)");
        ui.colored_label(E_PARTICLE_ORANGE, "  Orange = e-particles");
        ui.colored_label(FOREST_GREEN, "  Green = clean");
        ui.colored_label(GOLD_EG, "  Gold = non-contractible cycles");
    }

    fn draw_cnt_central(&mut self, ui: &mut egui::Ui, ctx: &egui::Context) {
        let full = ui.available_rect_before_wrap();
        let chart_h = (full.height() * 0.30).max(120.0);
        let top = egui::Rect::from_min_max(full.min, egui::pos2(full.max.x, full.max.y - chart_h));
        let bot = egui::Rect::from_min_max(egui::pos2(full.min.x, full.max.y - chart_h), full.max);
        let mid_x = top.center().x;
        let torus_rect = egui::Rect::from_min_max(top.min, egui::pos2(mid_x, top.max.y));
        let lat_rect = egui::Rect::from_min_max(egui::pos2(mid_x, top.min.y), top.max);

        // Interaction
        let torus_response = ui.allocate_rect(torus_rect, egui::Sense::click_and_drag());
        let lat_response = ui.allocate_rect(lat_rect, egui::Sense::click_and_drag());

        if torus_response.dragged() {
            let delta = torus_response.drag_delta();
            self.rotation[0] += delta.y * 0.008;
            self.rotation[1] += delta.x * 0.008;
            self.auto_rotate = false;
        }
        if torus_response.double_clicked() { self.auto_rotate = true; }
        if torus_response.hovered() { torus_response.on_hover_text("Drag to rotate | Double-click to reset"); }

        // Lattice hover
        let lattice_n_for_hit = self.cnt_snapshot.as_ref().map(|s| s.n);
        if let Some(n) = lattice_n_for_hit {
            if let Some(hover_pos) = lat_response.hover_pos() {
                self.cnt_hovered_node = hit_test_lattice(hover_pos, lat_rect, n);
            } else {
                self.cnt_hovered_node = None;
            }
        } else {
            self.cnt_hovered_node = None;
        }

        // Tooltip
        let tooltip_text = if let (Some((row, col)), Some(ref snap)) = (self.cnt_hovered_node, &self.cnt_snapshot) {
            let n = snap.n;
            let hi = row * n + col;
            let vi = n * n + row * n + col;
            let hx = snap.x_errors.get(hi).copied().unwrap_or(false);
            let hz = snap.z_errors.get(hi).copied().unwrap_or(false);
            let vx = snap.x_errors.get(vi).copied().unwrap_or(false);
            let vz = snap.z_errors.get(vi).copied().unwrap_or(false);
            let is_e = snap.e_particles.contains(&(row, col));
            let is_m = snap.m_particles.contains(&(row, col));
            Some(format!("Vertex ({}, {})\nH-edge: X={} Z={}\nV-edge: X={} Z={}\n{}{}", row, col, if hx { "err" } else { "ok" }, if hz { "err" } else { "ok" }, if vx { "err" } else { "ok" }, if vz { "err" } else { "ok" }, if is_e { "e-particle " } else { "" }, if is_m { "m-particle" } else { "" }))
        } else { None };
        if let Some(tip) = tooltip_text { lat_response.clone().on_hover_text(tip); }

        // Left-click toggle
        if lat_response.clicked() {
            if let Some((row, col)) = self.cnt_hovered_node {
                if let Some(ref mut snap) = self.cnt_snapshot {
                    let hi = row * snap.n + col;
                    if let Some(v) = snap.x_errors.get_mut(hi) { *v = !*v; }
                    let (e, m) = cnt_bridge::recompute_syndromes(snap);
                    snap.e_particles = e;
                    snap.m_particles = m;
                }
            }
        }

        // Right-click context menu
        let hovered = self.cnt_hovered_node;
        lat_response.clone().context_menu(|ui| {
            if let Some((row, col)) = hovered {
                ui.label(format!("Vertex ({}, {})", row, col));
                ui.separator();
                if ui.button("Toggle X error (H-edge)").clicked() {
                    if let Some(ref mut snap) = self.cnt_snapshot {
                        let hi = row * snap.n + col;
                        if let Some(v) = snap.x_errors.get_mut(hi) { *v = !*v; }
                        let (e, m) = cnt_bridge::recompute_syndromes(snap);
                        snap.e_particles = e; snap.m_particles = m;
                    }
                    ui.close_menu();
                }
                if ui.button("Toggle Z error (H-edge)").clicked() {
                    if let Some(ref mut snap) = self.cnt_snapshot {
                        let hi = row * snap.n + col;
                        if let Some(v) = snap.z_errors.get_mut(hi) { *v = !*v; }
                        let (e, m) = cnt_bridge::recompute_syndromes(snap);
                        snap.e_particles = e; snap.m_particles = m;
                    }
                    ui.close_menu();
                }
                if ui.button("Toggle X error (V-edge)").clicked() {
                    if let Some(ref mut snap) = self.cnt_snapshot {
                        let vi = snap.n * snap.n + row * snap.n + col;
                        if let Some(v) = snap.x_errors.get_mut(vi) { *v = !*v; }
                        let (e, m) = cnt_bridge::recompute_syndromes(snap);
                        snap.e_particles = e; snap.m_particles = m;
                    }
                    ui.close_menu();
                }
                if ui.button("Toggle Z error (V-edge)").clicked() {
                    if let Some(ref mut snap) = self.cnt_snapshot {
                        let vi = snap.n * snap.n + row * snap.n + col;
                        if let Some(v) = snap.z_errors.get_mut(vi) { *v = !*v; }
                        let (e, m) = cnt_bridge::recompute_syndromes(snap);
                        snap.e_particles = e; snap.m_particles = m;
                    }
                    ui.close_menu();
                }
            } else {
                ui.label("No vertex selected");
            }
        });

        // Drawing
        let painter = ui.painter();

        painter.text(torus_rect.center_top() + egui::vec2(0.0, 12.0), egui::Align2::CENTER_TOP, format!("3D TORUS (T\u{00b2})  \u{2014}  Tonnetz {0}\u{00d7}{0}", self.cnt_params.tonnetz_grid_size), egui::FontId::proportional(13.0), HEADING_CLR);
        painter.text(lat_rect.center_top() + egui::vec2(0.0, 12.0), egui::Align2::CENTER_TOP, format!("{0}\u{00d7}{0} TORIC CODE  \u{2014}  Pauli frame snapshot", self.cnt_lattice_n), egui::FontId::proportional(13.0), HEADING_CLR);

        draw_cnt_torus(painter, torus_rect, self.rotation, self.cnt_params.tonnetz_grid_size, self.cnt_snapshot.as_ref(), self.time);
        if let Some(ref snap) = self.cnt_snapshot {
            draw_lattice(painter, lat_rect, snap, self.cnt_hovered_node);
        }

        // Threshold chart
        painter.text(bot.center_top() + egui::vec2(0.0, 4.0), egui::Align2::CENTER_TOP, "THRESHOLD CURVE  \u{2014}  physical error rate p vs logical error rate P_L", egui::FontId::proportional(12.0), HEADING_CLR);

        let chart_inner = egui::Rect::from_min_max(bot.min + egui::vec2(10.0, 22.0), bot.max - egui::vec2(10.0, 5.0));
        let p_error = self.cnt_p_error;
        let logical_error_rate = self.cnt_logical_error_rate;

        ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart_inner), |ui| {
            let plot = Plot::new("cnt_threshold_chart")
                .width(chart_inner.width()).height(chart_inner.height())
                .x_axis_label("p (physical error rate)").y_axis_label("P_L")
                .include_x(0.0).include_x(0.2).include_y(0.0).include_y(1.0)
                .show_axes(true).allow_zoom(true).allow_drag(true).allow_scroll(true)
                .legend(Legend::default().position(Corner::LeftTop))
                .label_formatter(move |name, value| {
                    if !name.is_empty() { format!("{}\np = {:.4}\nP_L = {:.4}", name, value.x, value.y) }
                    else { format!("p = {:.4}\nP_L = {:.4}", value.x, value.y) }
                });

            plot.show(ui, |plot_ui| {
                // Correctable zone
                let zone_pts: PlotPoints = vec![[0.0, 0.0], [0.09, 0.0], [0.09, 1.0], [0.0, 1.0]].into_iter().collect();
                plot_ui.polygon(Polygon::new(zone_pts).fill_color(egui::Color32::from_rgba_unmultiplied(86, 166, 96, 20)).stroke(egui::Stroke::NONE).name("Correctable zone"));

                let colors = [FOREST_GREEN, GOLD_EG, egui::Color32::from_rgb(200, 200, 190), X_ERROR_RED];
                let markers = [MarkerShape::Circle, MarkerShape::Diamond, MarkerShape::Square, MarkerShape::Up];

                if let Some(ref cd) = self.cnt_chart_data {
                    for (i, curve) in cd.curves.iter().enumerate() {
                        let pts: PlotPoints = curve.points.iter().map(|&(p, pl)| [p, pl]).collect();
                        let scatter_pts: PlotPoints = curve.points.iter().map(|&(p, pl)| [p, pl]).collect();
                        let color = colors[i % colors.len()];
                        let marker = markers[i % markers.len()];
                        let name = format!("N={}", curve.n);
                        plot_ui.line(Line::new(pts).color(color).width(2.0).name(&name));
                        plot_ui.points(Points::new(scatter_pts).color(color).shape(marker).radius(3.5).name(&name));
                    }
                }

                if p_error > 0.0 {
                    plot_ui.vline(VLine::new(p_error).color(egui::Color32::WHITE).width(1.5).name("Operating point"));
                    plot_ui.text(PlotText::new(PlotPoint::new(p_error, logical_error_rate.max(0.05)), egui::RichText::new(format!("p={:.4}", p_error)).size(10.0).color(egui::Color32::WHITE)).anchor(egui::Align2::LEFT_BOTTOM));
                }
                plot_ui.vline(VLine::new(0.09).color(egui::Color32::from_rgba_unmultiplied(230, 70, 70, 120)).width(1.0).name("Threshold ~9%"));
                plot_ui.text(PlotText::new(PlotPoint::new(0.092, 0.92), egui::RichText::new("p_th ~ 9%").size(10.0).color(X_ERROR_RED)).anchor(egui::Align2::LEFT_TOP));
            });
        });

        let _ = ctx; // used for context menu
    }

    fn draw_cnt_status(&self, ctx: &egui::Context) {
        if let Some(ref phys) = self.cnt_physics_result {
            let (st, sc) = if self.cnt_p_error < 0.09 { ("CORRECTABLE", FOREST_GREEN) } else { ("TOO NOISY", WARN_RED) };
            let frame = egui::Frame {
                fill: egui::Color32::from_rgba_unmultiplied(22, 28, 22, 230),
                corner_radius: egui::CornerRadius::from(6),
                inner_margin: egui::Margin::same(10),
                stroke: egui::Stroke::new(2.0, sc),
                ..Default::default()
            };
            egui::Window::new("cnt_status").title_bar(false).resizable(false).movable(false).frame(frame).anchor(egui::Align2::RIGHT_BOTTOM, [-10.0, -10.0]).show(ctx, |ui| {
                ui.colored_label(sc, egui::RichText::new(st).strong().size(15.0));
                ui.label(format!("T\u{2082}={:.0}ns  p={:.4}  P_L={:.3}", phys.t2_ns, self.cnt_p_error, self.cnt_logical_error_rate));
                dim_label(ui, &format!("Tonnetz: +{:.0}ns ({:.0}\u{00d7})", phys.t2_ns - phys.t2_bare_ns, phys.tonnetz_enhancement));
                if self.paused { ui.colored_label(GOLD_EG, egui::RichText::new("PAUSED").size(11.0)); }
            });
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Hallucination Reduction tab methods
// ═══════════════════════════════════════════════════════════════════════════════

impl QuantumEngineApp {
    fn draw_drift_controls(&mut self, ui: &mut egui::Ui) {
        ui.colored_label(GOLD_EG, egui::RichText::new("HALLUCINATION REDUCTION").strong().size(13.0));
        dim_label(ui, "Toroidal logit bias on T\u{00b2}");
        ui.add_space(4.0);

        let mut changed = false;

        // ── Tonnetz Parameters ──
        section_heading(ui, "TONNETZ PARAMETERS");

        ui.label("Grid Size N");
        let mut n_f = self.drift_config.grid_n as f64;
        if ui.add(egui::Slider::new(&mut n_f, 4.0..=24.0).step_by(1.0).suffix("")).changed() {
            self.drift_config.grid_n = n_f as usize;
            changed = true;
        }

        ui.label("Walk Steps");
        let mut steps_f = self.drift_config.num_steps as f64;
        if ui.add(egui::Slider::new(&mut steps_f, 100.0..=5000.0).logarithmic(true).suffix("")).changed() {
            self.drift_config.num_steps = steps_f as usize;
            changed = true;
        }

        // ── Attention Mask ──
        section_heading(ui, "ATTENTION MASK");

        ui.label("Mask Type");
        ui.horizontal(|ui| {
            if ui.selectable_label(self.drift_config.mask_type == MaskType::HardCutoff, "Hard").clicked() {
                self.drift_config.mask_type = MaskType::HardCutoff;
                changed = true;
            }
            if ui.selectable_label(self.drift_config.mask_type == MaskType::SoftExponential, "Soft").clicked() {
                self.drift_config.mask_type = MaskType::SoftExponential;
                changed = true;
            }
            if ui.selectable_label(self.drift_config.mask_type == MaskType::Hybrid, "Hybrid").clicked() {
                self.drift_config.mask_type = MaskType::Hybrid;
                changed = true;
            }
        });

        ui.label("Radius r");
        if ui.add(egui::Slider::new(&mut self.drift_config.radius, 1.0..=8.0).step_by(0.5)).changed() {
            changed = true;
        }

        ui.label("Decay \u{03b1}");
        if ui.add(egui::Slider::new(&mut self.drift_config.alpha, 0.1..=2.0).step_by(0.1)).changed() {
            changed = true;
        }

        // ── Drift Metric ──
        section_heading(ui, "DRIFT METRIC");

        ui.label("Drift Threshold");
        let mut thresh_f = self.drift_config.drift_threshold as f64;
        if ui.add(egui::Slider::new(&mut thresh_f, 1.0..=8.0).step_by(1.0)).changed() {
            self.drift_config.drift_threshold = thresh_f as usize;
            changed = true;
        }

        // ── Visualization Mode ──
        section_heading(ui, "VISUALIZATION");
        ui.horizontal(|ui| {
            if ui.selectable_label(self.drift_viz_mode == DriftVizMode::Overview, "Overview").clicked() {
                self.drift_viz_mode = DriftVizMode::Overview;
            }
            if ui.selectable_label(self.drift_viz_mode == DriftVizMode::DriftAnalysis, "Drift").clicked() {
                self.drift_viz_mode = DriftVizMode::DriftAnalysis;
                if self.needs_drift_analysis { /* will fire in update */ }
            }
            if ui.selectable_label(self.drift_viz_mode == DriftVizMode::MaskAnalysis, "Mask").clicked() {
                self.drift_viz_mode = DriftVizMode::MaskAnalysis;
                if self.needs_mask_analysis { /* will fire in update */ }
            }
        });

        if changed {
            self.needs_drift_mc = true;
            self.needs_drift_heatmap = true;
            self.needs_drift_analysis = true;
            self.needs_mask_analysis = true;
        }

        // ── Mechanism ──
        ui.add_space(8.0);
        section_heading(ui, "MECHANISM");
        dim_label(ui, "The toroidal mask constrains attention");
        dim_label(ui, "to local neighborhoods on T\u{00b2}, preventing");
        dim_label(ui, "long-range semantic jumps that cause");
        dim_label(ui, "hallucination. Spectral gap \u{03bb}\u{2081}");
        dim_label(ui, "bounds the mixing rate, same as");
        dim_label(ui, "vacuum + qubit protection.");
    }

    fn draw_drift_results(&mut self, ui: &mut egui::Ui) {
        section_heading(ui, "DRIFT RATES");

        if let Some(ref dr) = self.drift_result {
            ui.horizontal(|ui| {
                ui.colored_label(FOREST_GREEN, "\u{25cf}");
                ui.label(format!("Toroidal: {:.3}", dr.toroidal_drift_rate));
            });
            ui.horizontal(|ui| {
                ui.colored_label(WARN_RED, "\u{25cf}");
                ui.label(format!("Baseline: {:.3}", dr.baseline_drift_rate));
            });
            ui.horizontal(|ui| {
                ui.colored_label(DIM, "\u{25cf}");
                ui.label(format!("Random:   {:.3}", dr.random_drift_rate));
            });

            ui.add_space(4.0);
            let rf_color = if dr.reduction_factor > 1.5 { FOREST_GREEN } else { GOLD_EG };
            ui.colored_label(rf_color, egui::RichText::new(format!("Reduction: {:.1}\u{00d7}", dr.reduction_factor)).strong());
        } else {
            dim_label(ui, "Computing...");
        }

        // ── Spectral Gap ──
        section_heading(ui, "SPECTRAL GAP");
        let gap = logit_drift::spectral_gap_runtime(self.drift_config.grid_n);
        ui.label(format!("\u{03bb}\u{2081} = {:.4}", gap));
        dim_label(ui, &format!("N={} Tonnetz torus", self.drift_config.grid_n));
        ui.add_space(2.0);
        dim_label(ui, "Same gap as vacuum + CNT tabs");

        // ── Mask Info ──
        section_heading(ui, "MASK CONFIG");
        let mask_name = match self.drift_config.mask_type {
            MaskType::HardCutoff => "Hard Cutoff",
            MaskType::SoftExponential => "Soft Exponential",
            MaskType::Hybrid => "Hybrid",
        };
        ui.label(format!("Type: {}", mask_name));
        ui.label(format!("r = {:.1}, \u{03b1} = {:.1}", self.drift_config.radius, self.drift_config.alpha));

        // ── Benchmark ──
        section_heading(ui, "TRUTHFULQA BENCHMARK");
        dim_label(ui, "Published results (817 samples):");
        ui.add_space(2.0);
        for entry in logit_drift::benchmark_data() {
            ui.horizontal(|ui| {
                let color = if entry.delta_pp >= 2.0 { FOREST_GREEN } else { LABEL_CLR };
                ui.colored_label(color, egui::RichText::new(format!("+{:.1}pp", entry.delta_pp)).strong().size(12.0));
                ui.label(egui::RichText::new(entry.model).size(11.0));
            });
        }
    }

    fn draw_drift_central(&mut self, ui: &mut egui::Ui) {
        let total_rect = ui.available_rect_before_wrap();
        let top_h = total_rect.height() * 0.55;
        let bottom_h = total_rect.height() - top_h;

        // ═══ TOP: 3D torus with drift trajectories ═══
        let torus_rect = egui::Rect::from_min_size(total_rect.min, egui::vec2(total_rect.width(), top_h));
        let painter = ui.painter_at(torus_rect);

        // Draw static torus (reuse CNT-style — no phase modulation)
        Self::draw_drift_torus(
            &painter,
            torus_rect,
            self.rotation,
            self.drift_config.grid_n,
            self.time,
            self.drift_result.as_ref(),
        );

        // ═══ BOTTOM: 3 panels (dispatch by viz mode) ═══
        let bw = total_rect.width() / 3.0;
        let bot_y = total_rect.min.y + top_h;

        let left_rect = egui::Rect::from_min_size(
            egui::pos2(total_rect.min.x, bot_y),
            egui::vec2(bw, bottom_h),
        );
        let center_rect = egui::Rect::from_min_size(
            egui::pos2(total_rect.min.x + bw, bot_y),
            egui::vec2(bw, bottom_h),
        );
        let right_rect = egui::Rect::from_min_size(
            egui::pos2(total_rect.min.x + 2.0 * bw, bot_y),
            egui::vec2(bw, bottom_h),
        );

        match self.drift_viz_mode {
            DriftVizMode::Overview => {
                self.draw_mask_heatmap(&painter, left_rect);
                let mut center_ui = ui.new_child(egui::UiBuilder::new().max_rect(center_rect));
                self.draw_spectral_decay_chart(&mut center_ui);
                let mut right_ui = ui.new_child(egui::UiBuilder::new().max_rect(right_rect));
                self.draw_benchmark_chart(&mut right_ui);
            }
            DriftVizMode::DriftAnalysis => {
                let mut left_ui = ui.new_child(egui::UiBuilder::new().max_rect(left_rect));
                self.draw_multi_scale_chart(&mut left_ui);
                let mut center_ui = ui.new_child(egui::UiBuilder::new().max_rect(center_rect));
                self.draw_phase_transition_chart(&mut center_ui);
                let mut right_ui = ui.new_child(egui::UiBuilder::new().max_rect(right_rect));
                self.draw_adjacency_chart(&mut right_ui);
            }
            DriftVizMode::MaskAnalysis => {
                let mut left_ui = ui.new_child(egui::UiBuilder::new().max_rect(left_rect));
                self.draw_sinkhorn_chart(&mut left_ui);
                let mut center_ui = ui.new_child(egui::UiBuilder::new().max_rect(center_rect));
                self.draw_sparsity_chart(&mut center_ui);
                self.draw_mask_heatmap(&painter, right_rect);
            }
        }
    }

    fn draw_drift_torus(
        painter: &egui::Painter,
        rect: egui::Rect,
        rot: [f32; 2],
        _grid_n: usize,
        time: f32,
        drift_result: Option<&DriftResult>,
    ) {
        let r_maj = 1.0f32;
        let r_min = 0.45f32;
        let rings = 24;
        let segs = 48;

        // Surface patches (simplified — wireframe + shading)
        for i in 0..rings {
            for j in 0..segs {
                let u0 = 2.0 * PI * i as f32 / rings as f32;
                let u1 = 2.0 * PI * (i + 1) as f32 / rings as f32;
                let v0 = 2.0 * PI * j as f32 / segs as f32;
                let v1 = 2.0 * PI * (j + 1) as f32 / segs as f32;

                let p00 = torus_pt(r_maj, r_min, u0, v0);
                let p10 = torus_pt(r_maj, r_min, u1, v0);
                let p01 = torus_pt(r_maj, r_min, u0, v1);
                let p11 = torus_pt(r_maj, r_min, u1, v1);

                let (s00, z00) = project(p00, rot, rect);
                let (s10, _) = project(p10, rot, rect);
                let (s01, _) = project(p01, rot, rect);
                let (s11, _) = project(p11, rot, rect);

                // Back-face culling
                let e1 = egui::vec2(s10.x - s00.x, s10.y - s00.y);
                let e2 = egui::vec2(s01.x - s00.x, s01.y - s00.y);
                let cross = e1.x * e2.y - e1.y * e2.x;
                if cross < 0.0 { continue; }

                let alpha = depth_alpha(z00);
                let base_g = 40 + (alpha as u16 * 30 / 200) as u8;
                let fill = egui::Color32::from_rgba_unmultiplied(20, base_g, 25, alpha / 3);
                painter.add(egui::Shape::convex_polygon(
                    vec![s00, s10, s11, s01],
                    fill,
                    egui::Stroke::NONE,
                ));
            }
        }

        // Wireframe rings
        for i in 0..=rings {
            let u = 2.0 * PI * i as f32 / rings as f32;
            for j in 0..segs {
                let v0 = 2.0 * PI * j as f32 / segs as f32;
                let v1 = 2.0 * PI * (j + 1) as f32 / segs as f32;
                let (a, za) = project(torus_pt(r_maj, r_min, u, v0), rot, rect);
                let (b, _) = project(torus_pt(r_maj, r_min, u, v1), rot, rect);
                let al = depth_alpha(za);
                painter.line_segment([a, b], egui::Stroke::new(0.5, egui::Color32::from_rgba_unmultiplied(60, 125, 85, al / 2)));
            }
        }
        for j in 0..=segs {
            let v = 2.0 * PI * j as f32 / segs as f32;
            for i in 0..rings {
                let u0 = 2.0 * PI * i as f32 / rings as f32;
                let u1 = 2.0 * PI * (i + 1) as f32 / rings as f32;
                let (a, za) = project(torus_pt(r_maj, r_min, u0, v), rot, rect);
                let (b, _) = project(torus_pt(r_maj, r_min, u1, v), rot, rect);
                let al = depth_alpha(za);
                painter.line_segment([a, b], egui::Stroke::new(0.5, egui::Color32::from_rgba_unmultiplied(60, 125, 85, al / 2)));
            }
        }

        // Non-contractible cycles (gold, pulsing)
        for &fixed_v in &[0.0f32, PI] {
            for k in 0..segs {
                let u0 = 2.0 * PI * k as f32 / segs as f32;
                let u1 = 2.0 * PI * (k + 1) as f32 / segs as f32;
                let (a, za) = project(torus_pt(r_maj, r_min, u0, fixed_v), rot, rect);
                let (b, _) = project(torus_pt(r_maj, r_min, u1, fixed_v), rot, rect);
                let pulse = 0.5 + 0.5 * (time * 1.5 + u0).sin();
                let al = (depth_alpha(za) as f32 * pulse) as u8;
                painter.line_segment([a, b], egui::Stroke::new(1.5, egui::Color32::from_rgba_unmultiplied(212, 175, 55, al)));
            }
        }
        for &fixed_u in &[0.0f32, PI] {
            for k in 0..segs {
                let v0 = 2.0 * PI * k as f32 / segs as f32;
                let v1 = 2.0 * PI * (k + 1) as f32 / segs as f32;
                let (a, za) = project(torus_pt(r_maj, r_min, fixed_u, v0), rot, rect);
                let (b, _) = project(torus_pt(r_maj, r_min, fixed_u, v1), rot, rect);
                let pulse = 0.5 + 0.5 * (time * 1.5 + v0).sin();
                let al = (depth_alpha(za) as f32 * pulse) as u8;
                painter.line_segment([a, b], egui::Stroke::new(1.5, egui::Color32::from_rgba_unmultiplied(212, 175, 55, al)));
            }
        }

        // Draw drift trajectories on the torus surface
        if let Some(dr) = drift_result {
            // Toroidal path — green
            Self::draw_path_on_torus(painter, rect, rot, r_maj, r_min, &dr.toroidal_path,
                egui::Color32::from_rgb(100, 230, 120), 2.0);
            // Baseline path — red
            Self::draw_path_on_torus(painter, rect, rot, r_maj, r_min, &dr.baseline_path,
                egui::Color32::from_rgb(230, 80, 80), 1.5);
        }

        // Title
        let title_pos = egui::pos2(rect.center().x, rect.min.y + 14.0);
        painter.text(title_pos, egui::Align2::CENTER_TOP,
            "Semantic Drift on T\u{00b2}",
            egui::FontId::proportional(13.0),
            HEADING_CLR);

        // Legend
        let legend_y = rect.min.y + 30.0;
        painter.text(egui::pos2(rect.min.x + 10.0, legend_y), egui::Align2::LEFT_TOP,
            "\u{25cf} Toroidal  \u{25cf} Baseline",
            egui::FontId::proportional(11.0),
            DIM);
        // Color dots for legend
        painter.circle_filled(egui::pos2(rect.min.x + 12.0, legend_y + 6.0), 3.0,
            egui::Color32::from_rgb(100, 230, 120));
        painter.circle_filled(egui::pos2(rect.min.x + 80.0, legend_y + 6.0), 3.0,
            egui::Color32::from_rgb(230, 80, 80));
    }

    fn draw_path_on_torus(
        painter: &egui::Painter,
        rect: egui::Rect,
        rot: [f32; 2],
        r_maj: f32,
        r_min: f32,
        path: &[(f32, f32)],
        color: egui::Color32,
        width: f32,
    ) {
        if path.len() < 2 { return; }
        for i in 0..(path.len() - 1) {
            let (u0, v0) = (path[i].0 * 2.0 * PI, path[i].1 * 2.0 * PI);
            let (u1, v1) = (path[i + 1].0 * 2.0 * PI, path[i + 1].1 * 2.0 * PI);
            let (a, za) = project(torus_pt(r_maj, r_min, u0, v0), rot, rect);
            let (b, _) = project(torus_pt(r_maj, r_min, u1, v1), rot, rect);
            let al = depth_alpha(za);
            let c = egui::Color32::from_rgba_unmultiplied(color.r(), color.g(), color.b(), al);
            painter.line_segment([a, b], egui::Stroke::new(width, c));
        }
        // Start marker
        let (u0, v0) = (path[0].0 * 2.0 * PI, path[0].1 * 2.0 * PI);
        let (start, _) = project(torus_pt(r_maj, r_min, u0, v0), rot, rect);
        painter.circle_filled(start, 4.0, egui::Color32::WHITE);
        // End marker
        let last = path.last().unwrap();
        let (ue, ve) = (last.0 * 2.0 * PI, last.1 * 2.0 * PI);
        let (end, _) = project(torus_pt(r_maj, r_min, ue, ve), rot, rect);
        painter.circle_filled(end, 4.0, color);
    }

    fn draw_mask_heatmap(&self, painter: &egui::Painter, rect: egui::Rect) {
        // Title
        let title_y = rect.min.y + 4.0;
        painter.text(egui::pos2(rect.center().x, title_y), egui::Align2::CENTER_TOP,
            "Mask Heatmap (center ref)",
            egui::FontId::proportional(12.0),
            HEADING_CLR);

        let margin = 24.0;
        let grid_rect = egui::Rect::from_min_size(
            egui::pos2(rect.min.x + margin, rect.min.y + margin),
            egui::vec2(rect.width() - 2.0 * margin, rect.height() - margin - 8.0),
        );

        if let Some(ref hm) = self.drift_heatmap {
            let n = hm.grid_n;
            let cell_w = grid_rect.width() / n as f32;
            let cell_h = grid_rect.height() / n as f32;

            for row in 0..n {
                for col in 0..n {
                    let val = hm.values[row][col];
                    let x = grid_rect.min.x + col as f32 * cell_w;
                    let y = grid_rect.min.y + row as f32 * cell_h;
                    let cell = egui::Rect::from_min_size(egui::pos2(x, y), egui::vec2(cell_w, cell_h));

                    // Color: dark blue (0) → forest green (0.5) → gold (1)
                    let color = if val < 0.5 {
                        let t = val * 2.0;
                        egui::Color32::from_rgb(
                            (15.0 + 71.0 * t) as u8,
                            (25.0 + 141.0 * t) as u8,
                            (60.0 + 36.0 * t) as u8,
                        )
                    } else {
                        let t = (val - 0.5) * 2.0;
                        egui::Color32::from_rgb(
                            (86.0 + 126.0 * t) as u8,
                            (166.0 + 9.0 * t) as u8,
                            (96.0 - 41.0 * t) as u8,
                        )
                    };
                    painter.rect_filled(cell, 0.0, color);

                    // Highlight ref position
                    if row == hm.ref_pos.0 && col == hm.ref_pos.1 {
                        painter.rect_stroke(cell, 0.0, egui::Stroke::new(2.0, egui::Color32::WHITE), egui::epaint::StrokeKind::Outside);
                    }
                }
            }
        } else {
            painter.text(grid_rect.center(), egui::Align2::CENTER_CENTER,
                "Computing...",
                egui::FontId::proportional(12.0),
                DIM);
        }
    }

    fn draw_spectral_decay_chart(&self, ui: &mut egui::Ui) {
        ui.colored_label(HEADING_CLR, egui::RichText::new("Spectral Decay e^(-\u{03bb}\u{2081}t)").size(12.0));

        let curves = logit_drift::spectral_decay_curves(&[8, 12, 16, 24], 5.0, 100);
        let colors = [FOREST_GREEN, GOLD_EG, egui::Color32::from_rgb(200, 200, 190), COMPRESS_BLUE];

        let plot = Plot::new("spectral_decay")
            .height(ui.available_height() - 20.0)
            .width(ui.available_width())
            .legend(Legend::default().position(Corner::RightTop))
            .x_axis_label("t")
            .y_axis_label("amplitude")
            .include_x(0.0)
            .include_x(5.0)
            .include_y(0.0)
            .include_y(1.0);

        plot.show(ui, |plot_ui| {
            for (i, (n, pts)) in curves.iter().enumerate() {
                let line_pts: PlotPoints = pts.iter().copied().collect();
                plot_ui.line(
                    Line::new(line_pts)
                        .color(colors[i % colors.len()])
                        .width(2.0)
                        .name(format!("N={}", n)),
                );
            }
        });
    }

    fn draw_benchmark_chart(&self, ui: &mut egui::Ui) {
        ui.colored_label(HEADING_CLR, egui::RichText::new("TruthfulQA T&I (pp improvement)").size(12.0));

        let entries = logit_drift::benchmark_data();

        let plot = Plot::new("benchmark_bars")
            .height(ui.available_height() - 20.0)
            .width(ui.available_width())
            .include_y(0.0)
            .include_y(3.5)
            .legend(Legend::default().position(Corner::RightTop));

        plot.show(ui, |plot_ui| {
            let bars: Vec<Bar> = entries.iter().enumerate().map(|(i, e)| {
                let color = if e.delta_pp >= 2.0 { FOREST_GREEN } else { GOLD_EG };
                Bar::new(i as f64, e.delta_pp as f64)
                    .width(0.6)
                    .fill(color)
                    .name(e.model)
            }).collect();
            plot_ui.bar_chart(BarChart::new(bars).name("Improvement (pp)"));
        });
    }

    // ─── 5 new advanced simulation charts ──────────────────────────────────

    fn draw_multi_scale_chart(&self, ui: &mut egui::Ui) {
        ui.colored_label(HEADING_CLR, egui::RichText::new("Multi-Scale Drift Comparison").size(12.0));

        if let Some(ref da) = self.drift_analysis {
            let plot = Plot::new("multi_scale_drift")
                .height(ui.available_height() - 20.0)
                .width(ui.available_width())
                .legend(Legend::default().position(Corner::RightTop))
                .include_y(0.0);

            plot.show(ui, |plot_ui| {
                let mut toroidal_bars = Vec::new();
                let mut baseline_bars = Vec::new();
                for (i, entry) in da.multi_scale.iter().enumerate() {
                    toroidal_bars.push(
                        Bar::new(i as f64 - 0.15, entry.toroidal_rate as f64)
                            .width(0.3)
                            .fill(FOREST_GREEN),
                    );
                    baseline_bars.push(
                        Bar::new(i as f64 + 0.15, entry.baseline_rate as f64)
                            .width(0.3)
                            .fill(WARN_RED),
                    );
                }
                plot_ui.bar_chart(BarChart::new(toroidal_bars).name("Toroidal"));
                plot_ui.bar_chart(BarChart::new(baseline_bars).name("Baseline"));

                // Spectral gap annotations
                for (i, entry) in da.multi_scale.iter().enumerate() {
                    let text = PlotText::new(
                        PlotPoint::new(i as f64, entry.baseline_rate as f64 + 0.02),
                        format!("\u{03bb}\u{2081}={:.3}", entry.spectral_gap),
                    ).color(GOLD_EG);
                    plot_ui.text(text);
                }
            });
        } else {
            dim_label(ui, "Computing...");
        }
    }

    fn draw_phase_transition_chart(&self, ui: &mut egui::Ui) {
        ui.colored_label(HEADING_CLR, egui::RichText::new("Phase Transition (Drift vs Radius)").size(12.0));

        if let Some(ref da) = self.drift_analysis {
            let plot = Plot::new("phase_transition")
                .height(ui.available_height() - 20.0)
                .width(ui.available_width())
                .x_axis_label("radius")
                .y_axis_label("drift rate")
                .include_y(0.0);

            let pts: Vec<[f64; 2]> = da.phase_transition.iter()
                .map(|e| [e.radius as f64, e.drift_rate as f64])
                .collect();

            // Find critical radius (steepest descent)
            let mut critical_r = da.phase_transition.first().map_or(1.0, |e| e.radius);
            let mut max_drop = 0.0f32;
            for w in da.phase_transition.windows(2) {
                let drop = w[0].drift_rate - w[1].drift_rate;
                if drop > max_drop {
                    max_drop = drop;
                    critical_r = (w[0].radius + w[1].radius) / 2.0;
                }
            }

            plot.show(ui, |plot_ui| {
                plot_ui.line(
                    Line::new(PlotPoints::from(pts))
                        .color(FOREST_GREEN)
                        .width(2.0)
                        .name("Drift Rate"),
                );
                plot_ui.vline(
                    VLine::new(critical_r as f64)
                        .color(GOLD_EG)
                        .width(1.5)
                        .name(format!("Critical r={:.1}", critical_r)),
                );
            });
        } else {
            dim_label(ui, "Computing...");
        }
    }

    fn draw_adjacency_chart(&self, ui: &mut egui::Ui) {
        ui.colored_label(HEADING_CLR, egui::RichText::new("Adjacency Loss (Local vs Global)").size(12.0));

        if let Some(ref da) = self.drift_analysis {
            let plot = Plot::new("adjacency_loss")
                .height(ui.available_height() - 20.0)
                .width(ui.available_width())
                .legend(Legend::default().position(Corner::RightTop))
                .x_axis_label("radius")
                .include_y(0.0);

            let pos_pts: Vec<[f64; 2]> = da.adjacency.iter()
                .map(|e| [e.radius as f64, e.pos_mean_dist as f64])
                .collect();
            let neg_pts: Vec<[f64; 2]> = da.adjacency.iter()
                .map(|e| [e.radius as f64, e.neg_mean_dist as f64])
                .collect();
            let loss_pts: Vec<[f64; 2]> = da.adjacency.iter()
                .map(|e| [e.radius as f64, e.loss as f64])
                .collect();

            plot.show(ui, |plot_ui| {
                plot_ui.line(
                    Line::new(PlotPoints::from(pos_pts))
                        .color(FOREST_GREEN)
                        .width(2.0)
                        .name("Positive (local)"),
                );
                plot_ui.line(
                    Line::new(PlotPoints::from(neg_pts))
                        .color(WARN_RED)
                        .width(2.0)
                        .name("Negative (random)"),
                );
                plot_ui.line(
                    Line::new(PlotPoints::from(loss_pts))
                        .color(GOLD_EG)
                        .width(1.5)
                        .style(egui_plot::LineStyle::dashed_dense())
                        .name("Loss"),
                );
            });
        } else {
            dim_label(ui, "Computing...");
        }
    }

    fn draw_sinkhorn_chart(&self, ui: &mut egui::Ui) {
        ui.colored_label(HEADING_CLR, egui::RichText::new("Sinkhorn-Knopp Convergence").size(12.0));

        if let Some(ref ma) = self.mask_analysis {
            let plot = Plot::new("sinkhorn_convergence")
                .height(ui.available_height() - 20.0)
                .width(ui.available_width())
                .x_axis_label("iteration")
                .y_axis_label("max error")
                .include_x(0.0)
                .include_x(50.0)
                .include_y(0.0);

            // Use log scale by transforming y values for display
            let pts: Vec<[f64; 2]> = ma.sinkhorn.points.iter()
                .map(|p| [p[0], p[1]])
                .collect();

            plot.show(ui, |plot_ui| {
                plot_ui.line(
                    Line::new(PlotPoints::from(pts))
                        .color(FOREST_GREEN)
                        .width(2.0)
                        .name("Max Error"),
                );
                // Convergence threshold line
                plot_ui.hline(
                    egui_plot::HLine::new(0.01)
                        .color(GOLD_EG)
                        .width(1.0)
                        .name("Threshold (0.01)"),
                );
                // Mark convergence point
                if ma.sinkhorn.converged_at < 50 {
                    let conv_y = ma.sinkhorn.points.get(ma.sinkhorn.converged_at.saturating_sub(1))
                        .map_or(0.01, |p| p[1]);
                    plot_ui.points(
                        Points::new(vec![[ma.sinkhorn.converged_at as f64, conv_y]])
                            .radius(6.0)
                            .color(GOLD_EG)
                            .shape(MarkerShape::Diamond)
                            .name(format!("Converged @ {}", ma.sinkhorn.converged_at)),
                    );
                }
            });
        } else {
            dim_label(ui, "Computing...");
        }
    }

    fn draw_sparsity_chart(&self, ui: &mut egui::Ui) {
        ui.colored_label(HEADING_CLR, egui::RichText::new("Sparsity vs Threshold").size(12.0));

        if let Some(ref ma) = self.mask_analysis {
            let plot = Plot::new("sparsity_sweep")
                .height(ui.available_height() - 20.0)
                .width(ui.available_width())
                .legend(Legend::default().position(Corner::RightTop))
                .include_y(0.0)
                .include_y(1.0);

            plot.show(ui, |plot_ui| {
                // Sparsity bars
                let bars: Vec<Bar> = ma.sparsity.iter().enumerate().map(|(i, e)| {
                    Bar::new(i as f64, e.sparsity as f64)
                        .width(0.6)
                        .fill(FOREST_GREEN)
                        .name(format!("t={:.3}", e.threshold))
                }).collect();
                plot_ui.bar_chart(BarChart::new(bars).name("Sparsity"));

                // Memory savings line (normalized to [0,1])
                let max_dense = ma.sparsity.first().map_or(1, |e| e.dense_memory).max(1);
                let mem_pts: Vec<[f64; 2]> = ma.sparsity.iter().enumerate().map(|(i, e)| {
                    [i as f64, e.memory_bytes as f64 / max_dense as f64]
                }).collect();
                plot_ui.line(
                    Line::new(PlotPoints::from(mem_pts))
                        .color(GOLD_EG)
                        .width(2.0)
                        .name("Memory (normalized)"),
                );
            });
        } else {
            dim_label(ui, "Computing...");
        }
    }

    fn draw_drift_status(&self, ctx: &egui::Context) {
        if let Some(ref dr) = self.drift_result {
            let (st, sc) = if dr.reduction_factor > 1.5 { ("EFFECTIVE", FOREST_GREEN) } else { ("MARGINAL", GOLD_EG) };
            let frame = egui::Frame {
                fill: egui::Color32::from_rgba_unmultiplied(22, 28, 22, 230),
                corner_radius: egui::CornerRadius::from(6),
                inner_margin: egui::Margin::same(10),
                stroke: egui::Stroke::new(2.0, sc),
                ..Default::default()
            };
            egui::Window::new("drift_status").title_bar(false).resizable(false).movable(false).frame(frame).anchor(egui::Align2::RIGHT_BOTTOM, [-10.0, -10.0]).show(ctx, |ui| {
                ui.colored_label(sc, egui::RichText::new(st).strong().size(15.0));
                ui.label(format!("{:.1}\u{00d7} reduction  \u{03bb}\u{2081}={:.4}  drift={:.3}",
                    dr.reduction_factor, dr.spectral_gap, dr.toroidal_drift_rate));
                if self.paused { ui.colored_label(GOLD_EG, egui::RichText::new("PAUSED").size(11.0)); }
            });
        }
    }
}
