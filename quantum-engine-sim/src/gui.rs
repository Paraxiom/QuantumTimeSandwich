//! egui UI: 3D torus, engine cycle visualization, charts, sliders, results readout.
//! Two-tab layout: Vacuum Engine and CNT Doppler cooling.

use std::f32::consts::PI;

use eframe::egui;
use egui_plot::{
    Bar, BarChart, Corner, Legend, Line, MarkerShape, Plot, PlotPoint, PlotPoints, Points, Polygon,
    Text as PlotText, VLine,
};

use crate::cnt_bridge::{self, ChartData, LatticeSnapshot};
use crate::cnt_physics::{BundleGeometry, Material, PhysicsParams, PhysicsResult, ResonatorType};
use crate::covariant::{DescentResult, DescentStep, NanoDescentTarget, TorusPoint};
use crate::engine::{EngineConfig, EngineResult};
use crate::logit_drift::{
    self, DriftAnalysisResult, DriftConfig, DriftResult, MaskAnalysisResult,
    MaskHeatmap as DriftHeatmap,
};
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
const TORUS_BLUE: egui::Color32 = egui::Color32::from_rgb(80, 160, 255);

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
    Nanotorus,
    HallucinationReduction,
    LogoDecoded,
    ToroidalEngine,
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

// ─── Torus knot drawing ─────────────────────────────────────────────────────

/// Draw a (p,q) torus knot on the torus surface.
/// p = windings around hole, q = windings through tube.
/// The curve follows: u(t) = p*t, v(t) = q*t for t ∈ [0, 2π].
fn draw_torus_knot(
    painter: &egui::Painter,
    rect: egui::Rect,
    rot: [f32; 2],
    r_maj: f32,
    r_min: f32,
    p: u32,
    q: u32,
    time: f32,
    color: egui::Color32,
    width: f32,
) {
    let steps = 360;
    let r_knot = r_min + 0.025;
    for i in 0..steps {
        let t0 = 2.0 * PI * i as f32 / steps as f32;
        let t1 = 2.0 * PI * (i + 1) as f32 / steps as f32;
        let u0 = p as f32 * t0;
        let v0 = q as f32 * t0;
        let u1 = p as f32 * t1;
        let v1 = q as f32 * t1;
        let (a, za) = project(torus_pt(r_maj, r_knot, u0, v0), rot, rect);
        let (b, _) = project(torus_pt(r_maj, r_knot, u1, v1), rot, rect);
        let al = depth_alpha(za);
        // Animated pulse along the knot
        let pulse = 0.6 + 0.4 * (time * 2.0 - t0 * 3.0).sin();
        let r = (color.r() as f32 * pulse) as u8;
        let g = (color.g() as f32 * pulse) as u8;
        let bl = (color.b() as f32 * pulse) as u8;
        painter.line_segment(
            [a, b],
            egui::Stroke::new(width, egui::Color32::from_rgba_unmultiplied(r, g, bl, al)),
        );
    }
}

const KNOT_CYAN: egui::Color32 = egui::Color32::from_rgb(120, 220, 255);

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
            let r = (pr as f32 * 0.4 + (20.0 + 50.0 * depth_t) * 0.6) as u8;
            let g = (pg as f32 * 0.4 + (60.0 + 80.0 * depth_t) * 0.6) as u8;
            let b = (pb as f32 * 0.4 + (50.0 + 30.0 * (1.0 - depth_t)) * 0.6) as u8;

            let mesh = egui::Mesh {
                indices: vec![0, 1, 2, 0, 2, 3],
                vertices: vec![
                    egui::epaint::Vertex {
                        pos: p00,
                        uv: egui::epaint::WHITE_UV,
                        color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                    },
                    egui::epaint::Vertex {
                        pos: p10,
                        uv: egui::epaint::WHITE_UV,
                        color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                    },
                    egui::epaint::Vertex {
                        pos: p11,
                        uv: egui::epaint::WHITE_UV,
                        color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                    },
                    egui::epaint::Vertex {
                        pos: p01,
                        uv: egui::epaint::WHITE_UV,
                        color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                    },
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
                (
                    torus_pt(rm, rn, fixed_other, a),
                    torus_pt(rm, rn, fixed_other, b),
                )
            } else {
                (
                    torus_pt(rm, rn, a, fixed_other),
                    torus_pt(rm, rn, b, fixed_other),
                )
            };
            let (sc1, _) = project(p1, rot, rect);
            let (sc2, _) = project(p2, rot, rect);
            let pulse = 0.55 + 0.45 * (a * 1.0 + time * if cycle_u { -2.0 } else { 1.5 }).sin();
            let r = (212.0 * pulse + 80.0 * (1.0 - pulse)) as u8;
            let g = (175.0 * pulse + 100.0 * (1.0 - pulse)) as u8;
            let bl = (55.0 * pulse + 30.0 * (1.0 - pulse)) as u8;
            painter.line_segment(
                [sc1, sc2],
                egui::Stroke::new(2.8, egui::Color32::from_rgb(r, g, bl)),
            );
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
            painter.circle_filled(
                sp,
                2.5,
                egui::Color32::from_rgba_unmultiplied(br, br, (br as f32 * 0.9) as u8, al),
            );
        }
    }

    // DCE photon sparks during extraction phase
    if matches!(phase, CyclePhase::Extract) {
        let spark_count = 12;
        for i in 0..spark_count {
            let spark_u = 2.0 * PI * (i as f32 + time * 5.0).rem_euclid(spark_count as f32)
                / spark_count as f32;
            let spark_v = 2.0 * PI * (i as f32 * 0.618 + time * 3.0).rem_euclid(1.0);
            let (sp, _z) = project(torus_pt(rm, rn + 0.06, spark_u, spark_v), rot, rect);
            let spark_alpha = (180.0 * phase_frac.min(1.0 - phase_frac) * 2.0) as u8;
            painter.circle_filled(
                sp,
                3.5,
                egui::Color32::from_rgba_unmultiplied(255, 220, 60, spark_alpha),
            );
            painter.circle_filled(
                sp,
                1.5,
                egui::Color32::from_rgba_unmultiplied(255, 255, 200, spark_alpha),
            );
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
                    egui::epaint::Vertex {
                        pos: p00,
                        uv: egui::epaint::WHITE_UV,
                        color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                    },
                    egui::epaint::Vertex {
                        pos: p10,
                        uv: egui::epaint::WHITE_UV,
                        color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                    },
                    egui::epaint::Vertex {
                        pos: p11,
                        uv: egui::epaint::WHITE_UV,
                        color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                    },
                    egui::epaint::Vertex {
                        pos: p01,
                        uv: egui::epaint::WHITE_UV,
                        color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                    },
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
                painter.line_segment(
                    [s1, s2],
                    egui::Stroke::new(0.7, egui::Color32::from_rgba_unmultiplied(wr, wg, wb, al)),
                );
            }
        }
    }

    // Non-contractible cycles
    for &(cycle_u, fixed_other) in &[(true, 0.0_f32), (true, PI), (false, 0.0), (false, PI)] {
        for s in 0..segs {
            let a = 2.0 * PI * s as f32 / segs as f32;
            let b = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;
            let (p1, p2) = if cycle_u {
                (
                    torus_pt(rm, rn, fixed_other, a),
                    torus_pt(rm, rn, fixed_other, b),
                )
            } else {
                (
                    torus_pt(rm, rn, a, fixed_other),
                    torus_pt(rm, rn, b, fixed_other),
                )
            };
            let (sc1, _) = project(p1, rot, rect);
            let (sc2, _) = project(p2, rot, rect);
            let pulse = 0.55 + 0.45 * (a + time * if cycle_u { -2.0 } else { 1.5 }).sin();
            let r = (212.0 * pulse + 80.0 * (1.0 - pulse)) as u8;
            let g = (175.0 * pulse + 100.0 * (1.0 - pulse)) as u8;
            let bl = (55.0 * pulse + 30.0 * (1.0 - pulse)) as u8;
            painter.line_segment(
                [sc1, sc2],
                egui::Stroke::new(2.8, egui::Color32::from_rgb(r, g, bl)),
            );
        }
    }

    // (3,2) torus knot — vibrational mode visualization
    draw_torus_knot(painter, rect, rot, rm, rn, 3, 2, time, KNOT_CYAN, 2.0);

    // Qubit nodes
    for row in 0..grid_n {
        for col in 0..grid_n {
            let u = 2.0 * PI * row as f32 / grid_n as f32;
            let v = 2.0 * PI * col as f32 / grid_n as f32;
            let (sp, z) = project(torus_pt(rm, rn + 0.015, u, v), rot, rect);
            let al = depth_alpha(z);
            let ph = 0.6 + 0.4 * (time * 2.0 + u + v).sin();
            let br = (210.0 * ph) as u8;
            painter.circle_filled(
                sp,
                2.5,
                egui::Color32::from_rgba_unmultiplied(br, br, (br as f32 * 0.9) as u8, al),
            );
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
    let inner = egui::Rect::from_min_max(
        rect.min + egui::vec2(m, m + 14.0),
        rect.max - egui::vec2(m, m),
    );
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
        painter.text(
            egui::pos2(x, inner.top() - 10.0),
            egui::Align2::CENTER_BOTTOM,
            format!("{}", col),
            egui::FontId::monospace(10.0),
            egui::Color32::from_rgb(100, 100, 95),
        );
    }
    for row in 0..n {
        let y = inner.top() + row as f32 * sy + sy * 0.5;
        painter.text(
            egui::pos2(inner.left() - 10.0, y),
            egui::Align2::RIGHT_CENTER,
            format!("{}", row),
            egui::FontId::monospace(10.0),
            egui::Color32::from_rgb(100, 100, 95),
        );
    }

    for row in 0..n {
        for col in 0..n {
            let x = inner.left() + col as f32 * sx + sx * 0.5;
            let y = inner.top() + row as f32 * sy + sy * 0.5;

            // Horizontal edge
            let hi = row * n + col;
            let hx = snapshot.x_errors.get(hi).copied().unwrap_or(false);
            let hz = snapshot.z_errors.get(hi).copied().unwrap_or(false);
            let x2 = if col + 1 < n {
                x + sx
            } else {
                inner.left() + sx * 0.5
            };
            painter.line_segment(
                [egui::pos2(x, y), egui::pos2(x2, y)],
                egui::Stroke::new(2.0, error_color(hx, hz)),
            );

            // Vertical edge
            let vi = n * n + row * n + col;
            let vx = snapshot.x_errors.get(vi).copied().unwrap_or(false);
            let vz = snapshot.z_errors.get(vi).copied().unwrap_or(false);
            let y2 = if row + 1 < n {
                y + sy
            } else {
                inner.top() + sy * 0.5
            };
            painter.line_segment(
                [egui::pos2(x, y), egui::pos2(x, y2)],
                egui::Stroke::new(2.0, error_color(vx, vz)),
            );

            // Hover highlight
            if hovered_node == Some((row, col)) {
                painter.circle_stroke(
                    egui::pos2(x, y),
                    8.0,
                    egui::Stroke::new(1.5, egui::Color32::WHITE),
                );
            }

            // Vertex marker
            let is_e = snapshot.e_particles.contains(&(row, col));
            let (vc, vr) = if is_e {
                (E_PARTICLE_ORANGE, 5.0)
            } else {
                (egui::Color32::from_rgb(86, 166, 96), 3.0)
            };
            painter.circle_filled(egui::pos2(x, y), vr, vc);

            // Plaquette marker
            if snapshot.m_particles.contains(&(row, col)) {
                painter.rect_filled(
                    egui::Rect::from_center_size(
                        egui::pos2(x + sx * 0.5, y + sy * 0.5),
                        egui::vec2(7.0, 7.0),
                    ),
                    1.0,
                    WARN_RED,
                );
            }
        }
    }
}

fn lattice_vertex_pos(rect: egui::Rect, n: usize, row: usize, col: usize) -> egui::Pos2 {
    let m = 25.0_f32;
    let inner = egui::Rect::from_min_max(
        rect.min + egui::vec2(m, m + 14.0),
        rect.max - egui::vec2(m, m),
    );
    let sx = inner.width() / n as f32;
    let sy = inner.height() / n as f32;
    egui::pos2(
        inner.left() + col as f32 * sx + sx * 0.5,
        inner.top() + row as f32 * sy + sy * 0.5,
    )
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

    // Nanotorus tab
    nano_params: PhysicsParams,
    nano_lattice_n: usize,
    nano_mc_trials: usize,
    nano_gate_time_ns: f64,
    nano_physics_result: Option<PhysicsResult>,
    nano_p_error: f64,
    nano_logical_error_rate: f64,
    nano_logical_failures: usize,
    nano_mc_trials_done: usize,
    nano_snapshot: Option<LatticeSnapshot>,
    nano_chart_data: Option<ChartData>,
    nano_descent_target: NanoDescentTarget,
    nano_descent_eta: f64,
    nano_descent_start: (f64, f64),
    nano_show_euclidean: bool,
    nano_descent_cov: Option<DescentResult>,
    nano_descent_euc: Option<DescentResult>,
    needs_nano_eval: bool,
    needs_nano_sweep: bool,
    nano_sweep_pending: bool,
    needs_nano_descent: bool,

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
    // Drift descent
    drift_descent_eta: f64,
    drift_descent_start: (f64, f64),
    drift_show_descent_euc: bool,
    drift_descent_cov: Option<DescentResult>,
    drift_descent_euc: Option<DescentResult>,
    needs_drift_descent: bool,

    // Logo Decoded tab
    logo_sphere_speed: f64,
    logo_torus_major: f32,
    logo_torus_minor: f32,
    logo_lattice_n: usize,
    logo_show_force: bool,
    logo_show_tonnetz: bool,
    logo_show_bloch_axes: bool,
    logo_show_triadic: bool,
    logo_sphere_angle: f32,

    // Toroidal Engine tab (sphere inside tube)
    te_torus_major: f32,
    te_torus_minor: f32,
    te_sphere_speed: f64, // angular velocity around the tube (toroidal)
    te_spin_speed: f64,   // sphere self-rotation speed
    te_lattice_n: usize,
    te_sphere_u: f32, // current toroidal angle of sphere
    te_sphere_v: f32, // current poloidal angle of sphere
    te_show_force: bool,
    te_show_tonnetz: bool,
    te_show_trail: bool,
    te_trail: Vec<[f32; 3]>, // trail of recent sphere positions

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
        style
            .text_styles
            .insert(egui::TextStyle::Heading, egui::FontId::proportional(17.0));
        style
            .text_styles
            .insert(egui::TextStyle::Body, egui::FontId::proportional(14.0));
        style
            .text_styles
            .insert(egui::TextStyle::Small, egui::FontId::proportional(12.0));
        style
            .text_styles
            .insert(egui::TextStyle::Monospace, egui::FontId::monospace(13.0));
        style
            .text_styles
            .insert(egui::TextStyle::Button, egui::FontId::proportional(14.0));
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

            nano_params: PhysicsParams::nanotorus_default(),
            nano_lattice_n: 6,
            nano_mc_trials: 500,
            nano_gate_time_ns: cnt_bridge::DEFAULT_GATE_TIME_NS,
            nano_physics_result: None,
            nano_p_error: 0.0,
            nano_logical_error_rate: 0.0,
            nano_logical_failures: 0,
            nano_mc_trials_done: 0,
            nano_snapshot: None,
            nano_chart_data: None,
            nano_descent_target: NanoDescentTarget::RingGeometry,
            nano_descent_eta: 0.005,
            nano_descent_start: (0.3, 0.3),
            nano_show_euclidean: true,
            nano_descent_cov: None,
            nano_descent_euc: None,
            needs_nano_eval: true,
            needs_nano_sweep: true,
            nano_sweep_pending: false,
            needs_nano_descent: true,

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
            drift_descent_eta: 0.005,
            drift_descent_start: (0.5, 0.5),
            drift_show_descent_euc: true,
            drift_descent_cov: None,
            drift_descent_euc: None,
            needs_drift_descent: false,

            logo_sphere_speed: 1.0,
            logo_torus_major: 1.2,
            logo_torus_minor: 0.45,
            logo_lattice_n: 8,
            logo_show_force: true,
            logo_show_tonnetz: true,
            logo_show_bloch_axes: true,
            logo_show_triadic: true,
            logo_sphere_angle: 0.0,

            te_torus_major: 1.2,
            te_torus_minor: 0.45,
            te_sphere_speed: 0.3,
            te_spin_speed: 1.5,
            te_lattice_n: 8,
            te_sphere_u: 0.0,
            te_sphere_v: 0.0,
            te_show_force: true,
            te_show_tonnetz: true,
            te_show_trail: true,
            te_trail: Vec::with_capacity(512),

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
        self.send_cnt_eval();
    }

    fn send_engine(&mut self) {
        self.worker.send(SimRequest::RunEngine {
            config: self.build_config(),
        });
        self.needs_engine = false;
    }

    fn send_descent(&mut self) {
        let start = TorusPoint::new(self.descent_start_x, self.descent_start_y);
        let target = TorusPoint::new(0.05, 0.95);
        self.worker.send(SimRequest::RunDescent {
            n: self.lattice_n,
            eta: self.descent_eta,
            start,
            target,
        });
        self.needs_descent = false;
    }

    fn send_scaling(&mut self) {
        self.worker.send(SimRequest::RunScaling {
            config: self.build_config(),
            sizes: vec![4, 6, 8, 10, 12, 16, 24],
        });
        self.needs_scaling = false;
    }

    fn send_convergence(&mut self) {
        self.worker.send(SimRequest::RunConvergence {
            sizes: vec![4, 6, 8, 12, 16, 24],
            eta: 0.001,
        });
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
        self.worker.send(SimRequest::RunDriftMC {
            config: self.drift_config.clone(),
        });
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

    fn send_nano_eval(&mut self) {
        self.worker.send(SimRequest::RunNanoEval {
            params: self.nano_params.clone(),
            lattice_n: self.nano_lattice_n,
            gate_time_ns: self.nano_gate_time_ns,
            mc_trials: self.nano_mc_trials,
        });
        self.needs_nano_eval = false;
    }

    fn send_nano_sweep(&mut self) {
        self.worker.send(SimRequest::RunCntSweep {
            lattice_n: self.nano_lattice_n,
            mc_trials: (self.nano_mc_trials / 5).max(50),
            operating_p: self.nano_p_error,
        });
        self.needs_nano_sweep = false;
        self.nano_sweep_pending = true;
    }

    fn send_nano_descent(&mut self) {
        let start = TorusPoint::new(self.nano_descent_start.0, self.nano_descent_start.1);
        self.worker.send(SimRequest::RunNanoDescent {
            base_params: self.nano_params.clone(),
            target: self.nano_descent_target,
            eta: self.nano_descent_eta,
            start,
            n_lattice: self.nano_lattice_n,
        });
        self.needs_nano_descent = false;
    }

    fn send_drift_descent(&mut self) {
        let start = TorusPoint::new(self.drift_descent_start.0, self.drift_descent_start.1);
        self.worker.send(SimRequest::RunDriftDescent {
            config: self.drift_config.clone(),
            eta: self.drift_descent_eta,
            start,
            n_lattice: self.drift_config.grid_n,
        });
        self.needs_drift_descent = false;
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
                SimResponse::Descent {
                    euclidean,
                    covariant,
                } => {
                    self.descent_euc = Some(euclidean);
                    self.descent_cov = Some(covariant);
                }
                SimResponse::Scaling(entries) => {
                    self.scaling_data = Some(entries);
                }
                SimResponse::Convergence(data) => {
                    self.convergence_data = Some(data);
                }
                SimResponse::CntEvaluated {
                    physics,
                    p_error,
                    mc_result,
                    snapshot,
                } => {
                    self.cnt_p_error = p_error;
                    self.cnt_logical_error_rate = mc_result.logical_error_rate;
                    self.cnt_logical_failures = mc_result.logical_failures;
                    self.cnt_mc_trials_done = mc_result.trials;
                    self.cnt_physics_result = Some(physics);
                    self.cnt_snapshot = Some(snapshot);
                    if !self.cnt_sweep_pending {
                        self.needs_cnt_sweep = true;
                    }
                }
                SimResponse::CntSweptChart(chart) => {
                    if self.nano_sweep_pending {
                        self.nano_chart_data = Some(chart);
                        self.nano_sweep_pending = false;
                    } else {
                        self.cnt_chart_data = Some(chart);
                        self.cnt_sweep_pending = false;
                    }
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
                SimResponse::NanoEvaluated {
                    physics,
                    p_error,
                    mc_result,
                    snapshot,
                } => {
                    self.nano_p_error = p_error;
                    self.nano_logical_error_rate = mc_result.logical_error_rate;
                    self.nano_logical_failures = mc_result.logical_failures;
                    self.nano_mc_trials_done = mc_result.trials;
                    self.nano_physics_result = Some(physics);
                    self.nano_snapshot = Some(snapshot);
                    if !self.nano_sweep_pending {
                        self.needs_nano_sweep = true;
                    }
                }
                SimResponse::NanoDescent {
                    covariant,
                    euclidean,
                } => {
                    self.nano_descent_cov = Some(covariant);
                    self.nano_descent_euc = Some(euclidean);
                }
                SimResponse::DriftDescent {
                    covariant,
                    euclidean,
                } => {
                    self.drift_descent_cov = Some(covariant);
                    self.drift_descent_euc = Some(euclidean);
                }
            }
        }

        // Fire nanotorus simulations when needed and tab is active
        if self.active_tab == Tab::Nanotorus {
            if self.needs_nano_eval {
                self.send_nano_eval();
            }
            if self.needs_nano_sweep && !self.nano_sweep_pending {
                self.send_nano_sweep();
            }
            if self.needs_nano_descent {
                self.send_nano_descent();
            }
        }

        // Fire drift simulations when needed and tab is active
        if self.active_tab == Tab::HallucinationReduction {
            if self.needs_drift_mc {
                self.send_drift_mc();
            }
            if self.needs_drift_heatmap {
                self.send_drift_heatmap();
            }
            if self.needs_drift_analysis && self.drift_viz_mode == DriftVizMode::DriftAnalysis {
                self.send_drift_analysis();
            }
            if self.needs_mask_analysis && self.drift_viz_mode == DriftVizMode::MaskAnalysis {
                self.send_mask_analysis();
            }
            if self.needs_drift_descent {
                self.send_drift_descent();
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
                        ui.colored_label(
                            GOLD_EG,
                            egui::RichText::new("PARAXIOM").strong().size(14.0),
                        );
                        ui.colored_label(DIM, egui::RichText::new("Technologies").size(12.0));
                    });
                    ui.add_space(2.0);

                    // Tab bar
                    ui.horizontal_wrapped(|ui| {
                        ui.selectable_value(
                            &mut self.active_tab,
                            Tab::VacuumEngine,
                            egui::RichText::new("Vacuum Engine").strong(),
                        );
                        ui.selectable_value(
                            &mut self.active_tab,
                            Tab::CntDoppler,
                            egui::RichText::new("CNT Doppler").strong(),
                        );
                        ui.selectable_value(
                            &mut self.active_tab,
                            Tab::Nanotorus,
                            egui::RichText::new("Nanotorus").strong().color(TORUS_BLUE),
                        );
                        ui.selectable_value(
                            &mut self.active_tab,
                            Tab::HallucinationReduction,
                            egui::RichText::new("Hallucination").strong(),
                        );
                        ui.selectable_value(
                            &mut self.active_tab,
                            Tab::LogoDecoded,
                            egui::RichText::new("Logo Decoded")
                                .strong()
                                .color(egui::Color32::from_rgb(167, 139, 250)),
                        );
                        ui.selectable_value(
                            &mut self.active_tab,
                            Tab::ToroidalEngine,
                            egui::RichText::new("Toroidal Engine")
                                .strong()
                                .color(LOGO_RED),
                        );
                    });
                    ui.separator();

                    // Pause/Resume
                    ui.horizontal(|ui| {
                        let (label, color) = if self.paused {
                            ("RESUME", FOREST_GREEN)
                        } else {
                            ("PAUSE", GOLD_EG)
                        };
                        if ui
                            .add(egui::Button::new(
                                egui::RichText::new(label).strong().color(color),
                            ))
                            .clicked()
                        {
                            self.paused = !self.paused;
                        }
                        ui.colored_label(
                            egui::Color32::from_rgb(110, 110, 105),
                            egui::RichText::new("(or Space)").size(11.0),
                        );
                    });
                    ui.add_space(4.0);

                    match self.active_tab {
                        Tab::VacuumEngine => self.draw_engine_controls(ui),
                        Tab::CntDoppler => self.draw_cnt_controls(ui),
                        Tab::Nanotorus => self.draw_nano_controls(ui),
                        Tab::HallucinationReduction => self.draw_drift_controls(ui),
                        Tab::LogoDecoded => self.draw_logo_controls(ui),
                        Tab::ToroidalEngine => self.draw_te_controls(ui),
                    }
                });
            });

        // ═════ RIGHT PANEL: Results (conditional on tab) ═════
        egui::SidePanel::right("results")
            .min_width(220.0)
            .max_width(280.0)
            .show(ctx, |ui| {
                egui::ScrollArea::vertical().show(ui, |ui| match self.active_tab {
                    Tab::VacuumEngine => self.draw_engine_results(ui),
                    Tab::CntDoppler => self.draw_cnt_results(ui),
                    Tab::Nanotorus => self.draw_nano_results(ui),
                    Tab::HallucinationReduction => self.draw_drift_results(ui),
                    Tab::LogoDecoded => self.draw_logo_results(ui),
                    Tab::ToroidalEngine => self.draw_te_results(ui),
                });
            });

        // ═════ CENTRAL PANEL: Visualizations (conditional on tab) ═════
        egui::CentralPanel::default()
            .frame(egui::Frame::NONE.fill(egui::Color32::from_rgb(20, 24, 20)))
            .show(ctx, |ui| match self.active_tab {
                Tab::VacuumEngine => self.draw_engine_central(ui),
                Tab::CntDoppler => self.draw_cnt_central(ui, ctx),
                Tab::Nanotorus => self.draw_nano_central(ui),
                Tab::HallucinationReduction => self.draw_drift_central(ui),
                Tab::LogoDecoded => self.draw_logo_central(ui),
                Tab::ToroidalEngine => self.draw_te_central(ui),
            });

        // Status badge (conditional on tab)
        match self.active_tab {
            Tab::VacuumEngine => self.draw_engine_status(ctx),
            Tab::CntDoppler => self.draw_cnt_status(ctx),
            Tab::Nanotorus => self.draw_nano_status(ctx),
            Tab::HallucinationReduction => self.draw_drift_status(ctx),
            Tab::LogoDecoded => self.draw_logo_status(ctx),
            Tab::ToroidalEngine => self.draw_te_status(ctx),
        }

        ctx.request_repaint();
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Vacuum Engine tab methods
// ═══════════════════════════════════════════════════════════════════════════════

impl QuantumEngineApp {
    fn draw_engine_controls(&mut self, ui: &mut egui::Ui) {
        ui.colored_label(
            GOLD_EG,
            egui::RichText::new("QUANTUM ENGINE VISUALIZER")
                .strong()
                .size(13.0),
        );
        dim_label(ui, "Toroidal vacuum engine on T\u{00b2}");
        ui.add_space(4.0);

        // Presets
        section_heading(ui, "PRESETS");
        let mut preset_clicked = false;
        ui.horizontal(|ui| {
            if ui
                .add(egui::Button::new(
                    egui::RichText::new("Microwave")
                        .color(COMPRESS_BLUE)
                        .size(12.0),
                ))
                .clicked()
            {
                self.apply_preset(&EngineConfig::microwave());
                preset_clicked = true;
            }
            if ui
                .add(egui::Button::new(
                    egui::RichText::new("Mid-IR")
                        .color(THERMAL_ORANGE)
                        .size(12.0),
                ))
                .clicked()
            {
                self.apply_preset(&EngineConfig::mid_infrared());
                preset_clicked = true;
            }
            if ui
                .add(egui::Button::new(
                    egui::RichText::new("Optical")
                        .color(EXTRACT_GOLD)
                        .size(12.0),
                ))
                .clicked()
            {
                self.apply_preset(&EngineConfig::optical());
                preset_clicked = true;
            }
        });

        // Cavity Parameters
        section_heading(ui, "CAVITY PARAMETERS");
        let mut engine_changed = preset_clicked;
        let freq_regime = if self.l_min_m > 1e-3 {
            "Microwave"
        } else if self.l_min_m > 1e-5 {
            "Mid-infrared"
        } else {
            "Optical"
        };
        dim_label(ui, &format!("Regime: {}", freq_regime));

        ui.add_space(4.0);
        ui.label("L_max (m)");
        dim_label(
            ui,
            &format!("Expanded cavity. {}", format_length(self.l_max_m)),
        );
        engine_changed |= ui
            .add(egui::Slider::new(&mut self.l_max_m, 1e-6..=0.1).logarithmic(true))
            .changed();

        ui.add_space(2.0);
        ui.label("L_min (m)");
        dim_label(
            ui,
            &format!("Compressed cavity. {}", format_length(self.l_min_m)),
        );
        engine_changed |= ui
            .add(egui::Slider::new(&mut self.l_min_m, 1e-6..=0.1).logarithmic(true))
            .changed();

        if self.l_min_m >= self.l_max_m {
            self.l_min_m = self.l_max_m * 0.98;
        }

        ui.add_space(2.0);
        ui.label("Temperature (K)");
        dim_label(ui, "Operating temperature.");
        engine_changed |= ui
            .add(egui::Slider::new(&mut self.temperature_k, 0.001..=300.0).logarithmic(true))
            .changed();

        ui.add_space(2.0);
        ui.label("\u{03b3} (Hz)");
        dim_label(ui, "Decoherence rate = \u{03c9}/Q.");
        engine_changed |= ui
            .add(egui::Slider::new(&mut self.decoherence_rate, 0.1..=1e9).logarithmic(true))
            .changed();

        ui.add_space(2.0);
        ui.label("\u{03b4}L/L (10^x)");
        dim_label(ui, "Modulation depth for DCE.");
        engine_changed |= ui
            .add(egui::Slider::new(&mut self.modulation_depth_exp, -8.0..=-2.0).step_by(0.5))
            .changed();

        // Lattice
        section_heading(ui, "LATTICE");
        ui.add_space(4.0);
        ui.label("N (lattice dimension)");
        dim_label(ui, "N\u{00d7}N torus.");
        let lattice_changed = ui
            .add(egui::Slider::new(&mut self.lattice_n, 4..=32))
            .changed();
        engine_changed |= lattice_changed;

        // Covariant Descent
        section_heading(ui, "COVARIANT DESCENT");
        dim_label(ui, "Gradient descent on T\u{00b2} surface.");
        let mut descent_changed = false;
        ui.add_space(4.0);
        ui.label("Learning rate \u{03b7}");
        descent_changed |= ui
            .add(egui::Slider::new(&mut self.descent_eta, 0.0001..=0.05).logarithmic(true))
            .changed();
        ui.add_space(2.0);
        ui.label("Start x");
        descent_changed |= ui
            .add(egui::Slider::new(&mut self.descent_start_x, 0.0..=1.0))
            .changed();
        ui.add_space(2.0);
        ui.label("Start y");
        descent_changed |= ui
            .add(egui::Slider::new(&mut self.descent_start_y, 0.0..=1.0))
            .changed();
        ui.add_space(2.0);
        ui.checkbox(&mut self.show_euclidean, "Show Euclidean path");
        descent_changed |= lattice_changed;

        if engine_changed {
            self.needs_engine = true;
            self.needs_scaling = true;
        }
        if descent_changed {
            self.needs_descent = true;
        }
        if lattice_changed {
            self.needs_convergence = true;
        }

        if self.needs_engine {
            self.send_engine();
        }
        if self.needs_descent {
            self.send_descent();
        }
        if self.needs_scaling {
            self.send_scaling();
        }
        if self.needs_convergence {
            self.send_convergence();
        }

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
            ui.label(format!(
                "\u{03b4}L\u{00b7}\u{03c9}/c = {:.2e}",
                r.perturbative_param
            ));

            let pert_color = if r.perturbative_param < 0.01 {
                FOREST_GREEN
            } else {
                WARN_RED
            };
            let pert_label = if r.perturbative_param < 0.01 {
                "PERTURBATIVE"
            } else {
                "NON-PERTURBATIVE"
            };
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
            let net_color = if r.cycle.net_work > 0.0 {
                FOREST_GREEN
            } else {
                WARN_RED
            };
            ui.colored_label(net_color, format!("Net work:   {:.3e} J", r.cycle.net_work));
            ui.label(format!("Power:      {:.3e} W", r.power_output));

            ui.add_space(6.0);
            section_heading(ui, "EFFICIENCY");
            ui.label(format!("\u{03b7} = {:.4e}", r.cycle.efficiency));
            dim_label(ui, "  With topological protection");
            ui.label(format!(
                "\u{03b7}\u{2080} = {:.4e}",
                r.efficiency_unprotected
            ));
            dim_label(ui, "  Without protection");
            if r.cycle.efficiency != 0.0 && r.efficiency_unprotected != 0.0 {
                let ratio = r.cycle.efficiency / r.efficiency_unprotected;
                let rc = if ratio > 1.0 { FOREST_GREEN } else { WARN_RED };
                ui.colored_label(
                    rc,
                    format!("\u{03b7}/\u{03b7}\u{2080} = {:.2}\u{00d7}", ratio),
                );
            }

            ui.add_space(6.0);
            section_heading(ui, "COHERENCE");
            let ec = if r.coherence_enhancement > 1.0 {
                FOREST_GREEN
            } else {
                GOLD_EG
            };
            ui.colored_label(
                ec,
                format!("Enhancement: {:.2}\u{00d7}", r.coherence_enhancement),
            );
            dim_label(ui, "  Tonnetz vs bare T\u{2082}");
            ui.label(format!(
                "Unruh a_min: {:.2e} m/s\u{00b2}",
                r.unruh_acceleration_threshold
            ));
        } else {
            dim_label(ui, "Computing...");
        }

        // Descent results
        ui.add_space(6.0);
        section_heading(ui, "DESCENT COMPARISON");
        if let Some(ref cov) = self.descent_cov {
            let conv_str = match cov.convergence_step {
                Some(s) => format!("step {}", s),
                None => "not converged".to_string(),
            };
            ui.colored_label(FOREST_GREEN, "Covariant (T\u{00b2}):");
            ui.label(format!("  Loss: {:.6}", cov.final_loss));
            ui.label(format!("  Conv: {}", conv_str));
            ui.label(format!("  Rate: {:.6}", cov.measured_rate));
        }
        if let Some(ref euc) = self.descent_euc {
            let conv_str = match euc.convergence_step {
                Some(s) => format!("step {}", s),
                None => "not converged".to_string(),
            };
            ui.colored_label(WARN_RED, "Euclidean (flat):");
            ui.label(format!("  Loss: {:.6}", euc.final_loss));
            ui.label(format!("  Conv: {}", conv_str));
            ui.label(format!("  Rate: {:.6}", euc.measured_rate));
        }
    }

    fn draw_engine_central(&self, ui: &mut egui::Ui) {
        let full = ui.available_rect_before_wrap();
        let torus_h = (full.height() * 0.55).max(200.0);
        let torus_rect =
            egui::Rect::from_min_max(full.min, egui::pos2(full.max.x, full.min.y + torus_h));
        let chart_area =
            egui::Rect::from_min_max(egui::pos2(full.min.x, full.min.y + torus_h), full.max);
        let col_w = chart_area.width() / 3.0;
        let chart1 = egui::Rect::from_min_max(
            chart_area.min,
            egui::pos2(chart_area.min.x + col_w, chart_area.max.y),
        );
        let chart2 = egui::Rect::from_min_max(
            egui::pos2(chart_area.min.x + col_w, chart_area.min.y),
            egui::pos2(chart_area.min.x + 2.0 * col_w, chart_area.max.y),
        );
        let chart3 = egui::Rect::from_min_max(
            egui::pos2(chart_area.min.x + 2.0 * col_w, chart_area.min.y),
            chart_area.max,
        );

        let torus_response = ui.allocate_rect(torus_rect, egui::Sense::click_and_drag());
        if torus_response.dragged() {
            // rotation is handled via interior mutability workaround — but since &self, we skip drag here
            // (drag is handled in the main update for the torus_rect area)
        }

        {
            let painter = ui.painter();
            let (phase, _) = cycle_phase(self.time);
            let phase_name = match phase {
                CyclePhase::Compress => "COMPRESS",
                CyclePhase::Extract => "EXTRACT",
                CyclePhase::Expand => "EXPAND",
                CyclePhase::Idle => "IDLE",
            };
            let phase_col = match phase {
                CyclePhase::Compress => COMPRESS_BLUE,
                CyclePhase::Extract => EXTRACT_GOLD,
                CyclePhase::Expand => EXPAND_GREEN,
                CyclePhase::Idle => DIM,
            };
            painter.text(
                torus_rect.center_top() + egui::vec2(0.0, 12.0),
                egui::Align2::CENTER_TOP,
                format!(
                    "3D TORUS (T\u{00b2}) \u{2014} {0}\u{00d7}{0} lattice",
                    self.lattice_n
                ),
                egui::FontId::proportional(13.0),
                HEADING_CLR,
            );
            painter.text(
                torus_rect.center_top() + egui::vec2(0.0, 28.0),
                egui::Align2::CENTER_TOP,
                format!("Engine phase: {}", phase_name),
                egui::FontId::proportional(11.0),
                phase_col,
            );

            let cov_steps = self.descent_cov.as_ref().map(|d| d.steps.as_slice());
            let euc_steps = self.descent_euc.as_ref().map(|d| d.steps.as_slice());
            draw_engine_torus(
                painter,
                torus_rect,
                self.rotation,
                self.lattice_n,
                self.time,
                cov_steps,
                euc_steps,
                self.show_euclidean,
            );

            painter.text(
                chart1.center_top() + egui::vec2(0.0, 4.0),
                egui::Align2::CENTER_TOP,
                "ENGINE CYCLE ENERGY",
                egui::FontId::proportional(11.0),
                HEADING_CLR,
            );
            painter.text(
                chart2.center_top() + egui::vec2(0.0, 4.0),
                egui::Align2::CENTER_TOP,
                "CONVERGENCE RATE vs \u{03bb}\u{2081}",
                egui::FontId::proportional(11.0),
                HEADING_CLR,
            );
            painter.text(
                chart3.center_top() + egui::vec2(0.0, 4.0),
                egui::Align2::CENTER_TOP,
                "SCALING: \u{03b7}, DCE, Enhancement vs N",
                egui::FontId::proportional(11.0),
                HEADING_CLR,
            );
        }

        // Chart 1: Energy Budget
        let chart1_inner = egui::Rect::from_min_max(
            chart1.min + egui::vec2(8.0, 20.0),
            chart1.max - egui::vec2(8.0, 5.0),
        );
        ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart1_inner), |ui| {
            Plot::new("energy_budget")
                .width(chart1_inner.width())
                .height(chart1_inner.height())
                .y_axis_label("Energy (J)")
                .show_axes(true)
                .allow_zoom(true)
                .allow_drag(true)
                .legend(Legend::default().position(Corner::RightTop))
                .show(ui, |plot_ui| {
                    if let Some(ref r) = self.engine_result {
                        let bars = vec![
                            Bar::new(0.0, r.cycle.work_compression)
                                .name("W_compress")
                                .fill(COMPRESS_BLUE),
                            Bar::new(1.0, r.cycle.energy_extracted)
                                .name("E_extract")
                                .fill(EXTRACT_GOLD),
                            Bar::new(2.0, r.cycle.decoherence_loss)
                                .name("Decoherence")
                                .fill(LOSS_RED),
                            Bar::new(3.0, r.cycle.thermal_noise)
                                .name("Thermal")
                                .fill(THERMAL_ORANGE),
                            Bar::new(4.0, r.cycle.net_work.max(0.0))
                                .name("Net work")
                                .fill(FOREST_GREEN),
                        ];
                        plot_ui.bar_chart(BarChart::new(bars).width(0.7));
                    }
                });
        });

        // Chart 2: Convergence Rate vs λ₁
        let chart2_inner = egui::Rect::from_min_max(
            chart2.min + egui::vec2(8.0, 20.0),
            chart2.max - egui::vec2(8.0, 5.0),
        );
        ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart2_inner), |ui| {
            Plot::new("convergence_chart")
                .width(chart2_inner.width())
                .height(chart2_inner.height())
                .x_axis_label("\u{03bb}\u{2081}")
                .y_axis_label("Measured rate")
                .show_axes(true)
                .allow_zoom(true)
                .allow_drag(true)
                .legend(Legend::default().position(Corner::LeftTop))
                .show(ui, |plot_ui| {
                    if let Some(ref data) = self.convergence_data {
                        let pts: PlotPoints = data.iter().map(|&(_, l, m)| [l, m]).collect();
                        plot_ui.points(
                            Points::new(pts)
                                .color(FOREST_GREEN)
                                .radius(5.0)
                                .name("rate vs \u{03bb}\u{2081}"),
                        );
                        for &(n, l, m) in data {
                            plot_ui.text(
                                PlotText::new(
                                    PlotPoint::new(l, m),
                                    egui::RichText::new(format!("N={}", n)).size(9.0).color(DIM),
                                )
                                .anchor(egui::Align2::LEFT_BOTTOM),
                            );
                        }
                        if let Some(&(_, l0, m0)) = data.first() {
                            if l0 > 0.0 {
                                let k = m0 / l0;
                                let max_l = data.iter().map(|&(_, l, _)| l).fold(0.0_f64, f64::max);
                                plot_ui.line(
                                    Line::new(PlotPoints::from(vec![
                                        [0.0, 0.0],
                                        [max_l, k * max_l],
                                    ]))
                                    .color(GOLD_EG)
                                    .width(1.5)
                                    .name("rate \u{221d} \u{03bb}\u{2081}"),
                                );
                            }
                        }
                    }
                });
        });

        // Chart 3: Scaling Study
        let chart3_inner = egui::Rect::from_min_max(
            chart3.min + egui::vec2(8.0, 20.0),
            chart3.max - egui::vec2(8.0, 5.0),
        );
        ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart3_inner), |ui| {
            Plot::new("scaling_chart")
                .width(chart3_inner.width())
                .height(chart3_inner.height())
                .x_axis_label("N")
                .show_axes(true)
                .allow_zoom(true)
                .allow_drag(true)
                .legend(Legend::default().position(Corner::LeftTop))
                .show(ui, |plot_ui| {
                    if let Some(ref data) = self.scaling_data {
                        let enh_line: PlotPoints = data
                            .iter()
                            .map(|e| [e.n as f64, e.coherence_enhancement])
                            .collect();
                        let enh_scatter: PlotPoints = data
                            .iter()
                            .map(|e| [e.n as f64, e.coherence_enhancement])
                            .collect();
                        plot_ui.line(
                            Line::new(enh_line)
                                .color(FOREST_GREEN)
                                .width(2.0)
                                .name("Enhancement (\u{00d7})"),
                        );
                        plot_ui.points(
                            Points::new(enh_scatter)
                                .color(FOREST_GREEN)
                                .radius(4.0)
                                .name("Enhancement"),
                        );
                        let max_dce = data.iter().map(|e| e.dce_pair_rate).fold(0.0_f64, f64::max);
                        if max_dce > 0.0 {
                            let dce_pts: PlotPoints = data
                                .iter()
                                .map(|e| {
                                    [
                                        e.n as f64,
                                        e.dce_pair_rate / max_dce
                                            * data
                                                .iter()
                                                .map(|x| x.coherence_enhancement)
                                                .fold(0.0_f64, f64::max),
                                    ]
                                })
                                .collect();
                            plot_ui.line(
                                Line::new(dce_pts)
                                    .color(GOLD_EG)
                                    .width(2.0)
                                    .name("DCE (normalized)"),
                            );
                        }
                        let max_gap = data.iter().map(|e| e.spectral_gap).fold(0.0_f64, f64::max);
                        let max_enh = data
                            .iter()
                            .map(|e| e.coherence_enhancement)
                            .fold(0.0_f64, f64::max);
                        if max_gap > 0.0 {
                            let gap_pts: PlotPoints = data
                                .iter()
                                .map(|e| [e.n as f64, e.spectral_gap / max_gap * max_enh])
                                .collect();
                            plot_ui.line(
                                Line::new(gap_pts)
                                    .color(egui::Color32::from_rgb(200, 200, 190))
                                    .width(1.5)
                                    .name("\u{03bb}\u{2081} (scaled)"),
                            );
                        }
                    }
                });
        });
    }

    fn draw_engine_status(&self, ctx: &egui::Context) {
        if let Some(ref r) = self.engine_result {
            let (st, sc) = if r.perturbative_param < 0.01 {
                ("PERTURBATIVE", FOREST_GREEN)
            } else {
                ("NON-PERTURBATIVE", WARN_RED)
            };
            let frame = egui::Frame {
                fill: egui::Color32::from_rgba_unmultiplied(22, 28, 22, 230),
                corner_radius: egui::CornerRadius::from(6),
                inner_margin: egui::Margin::same(10),
                stroke: egui::Stroke::new(2.0, sc),
                ..Default::default()
            };
            egui::Window::new("status")
                .title_bar(false)
                .resizable(false)
                .movable(false)
                .frame(frame)
                .anchor(egui::Align2::RIGHT_BOTTOM, [-10.0, -10.0])
                .show(ctx, |ui| {
                    ui.colored_label(sc, egui::RichText::new(st).strong().size(15.0));
                    ui.label(format!(
                        "\u{03b7}={:.2e}  \u{03bb}\u{2081}={:.4}  enhance={:.1}\u{00d7}",
                        r.cycle.efficiency, r.cycle.spectral_gap, r.coherence_enhancement
                    ));
                    dim_label(
                        ui,
                        &format!("P={:.2e}W  n_th={:.1e}", r.power_output, r.thermal_photons),
                    );
                    if self.paused {
                        ui.colored_label(GOLD_EG, egui::RichText::new("PAUSED").size(11.0));
                    }
                });
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  CNT Doppler tab methods
// ═══════════════════════════════════════════════════════════════════════════════

impl QuantumEngineApp {
    fn draw_cnt_controls(&mut self, ui: &mut egui::Ui) {
        ui.colored_label(
            GOLD_EG,
            egui::RichText::new("DOPPLER-TORIC SIMULATOR")
                .strong()
                .size(13.0),
        );
        dim_label(ui, "Physical layer \u{2192} logical layer bridge");
        ui.add_space(4.0);

        section_heading(ui, "PRESETS");
        let mut preset_changed = false;
        ui.horizontal(|ui| {
            if ui
                .add(egui::Button::new(
                    egui::RichText::new("Optimal")
                        .color(FOREST_GREEN)
                        .size(12.0),
                ))
                .clicked()
            {
                // Short SWCNT in dilution fridge + high laser + strong Tonnetz
                self.cnt_params.resonator_type = ResonatorType::Nanotube;
                self.cnt_params.material = Material::Carbon;
                self.cnt_params.cnt_length_nm = 300.0;
                self.cnt_params.cnt_diameter_nm = 1.4;
                self.cnt_params.num_walls = 1;
                self.cnt_params.cavity_finesse = 50000.0;
                self.cnt_params.temperature = 0.020;
                self.cnt_params.laser_power = 20.0;
                self.cnt_params.detuning = -1.0;
                self.cnt_params.kappa = 0.5;
                self.cnt_params.piezo_voltage = 5.0;
                self.cnt_params.tonnetz_grid_size = 12;
                self.cnt_params.tonnetz_q = 100.0;
                self.cnt_lattice_n = 6;
                self.cnt_mc_trials = 500;
                self.cnt_gate_time_ns = 50.0;
                preset_changed = true;
            }
            if ui
                .add(egui::Button::new(
                    egui::RichText::new("Room Temp").color(WARN_RED).size(12.0),
                ))
                .clicked()
            {
                self.cnt_params = PhysicsParams::default();
                self.cnt_lattice_n = 6;
                self.cnt_mc_trials = 500;
                self.cnt_gate_time_ns = cnt_bridge::DEFAULT_GATE_TIME_NS;
                preset_changed = true;
            }
        });

        section_heading(ui, "MATERIAL");
        let mut changed = preset_changed;
        {
            let prev = self.cnt_params.material;
            egui::ComboBox::from_id_salt("cnt_material")
                .selected_text(self.cnt_params.material.label())
                .show_ui(ui, |ui| {
                    ui.selectable_value(&mut self.cnt_params.material, Material::Carbon, "Carbon");
                    ui.selectable_value(
                        &mut self.cnt_params.material,
                        Material::BoronNitride,
                        "Boron Nitride",
                    );
                    ui.selectable_value(
                        &mut self.cnt_params.material,
                        Material::MoS2,
                        "MoS\u{2082}",
                    );
                    ui.selectable_value(
                        &mut self.cnt_params.material,
                        Material::SiliconCarbide,
                        "Silicon Carbide",
                    );
                });
            if self.cnt_params.material != prev {
                changed = true;
            }
            let desc = match self.cnt_params.material {
                Material::Carbon => "E=1.0 TPa, \u{03c1}=2200 kg/m\u{00b3}",
                Material::BoronNitride => "E=0.8 TPa, \u{03c1}=2100, low charge noise",
                Material::MoS2 => "E=0.27 TPa, \u{03c1}=5060, semiconducting",
                Material::SiliconCarbide => "E=0.45 TPa, \u{03c1}=3210, excellent thermal",
            };
            dim_label(ui, desc);
        }

        section_heading(ui, "NANOTUBE GEOMETRY");

        // CNT tab always uses Nanotube
        self.cnt_params.resonator_type = ResonatorType::Nanotube;

        ui.add_space(4.0);
        ui.label("Length (nm)");
        dim_label(ui, "Shorter \u{2192} higher frequency.");
        changed |= ui
            .add(
                egui::Slider::new(&mut self.cnt_params.cnt_length_nm, 100.0..=5000.0)
                    .logarithmic(true),
            )
            .changed();

        ui.add_space(2.0);
        ui.label("Tube Diameter (nm)");
        dim_label(ui, "SWCNT ~1\u{2013}2nm, MWCNT ~5\u{2013}50nm.");
        changed |= ui
            .add(
                egui::Slider::new(&mut self.cnt_params.cnt_diameter_nm, 0.5..=50.0)
                    .logarithmic(true),
            )
            .changed();

        ui.add_space(2.0);
        ui.label("Walls");
        dim_label(ui, "1=SWCNT, 2+=MWCNT. More walls \u{2192} lower Q.");
        let mut walls_f = self.cnt_params.num_walls as f64;
        if ui
            .add(egui::Slider::new(&mut walls_f, 1.0..=10.0).step_by(1.0))
            .changed()
        {
            self.cnt_params.num_walls = walls_f as usize;
            changed = true;
        }

        ui.add_space(2.0);
        ui.label("Cavity Finesse");
        dim_label(ui, "Higher \u{2192} narrower linewidth, better resolved.");
        changed |= ui
            .add(
                egui::Slider::new(&mut self.cnt_params.cavity_finesse, 100.0..=100000.0)
                    .logarithmic(true),
            )
            .changed();

        // Show derived quantities
        if let Some(ref phys) = self.cnt_physics_result {
            ui.add_space(2.0);
            dim_label(
                ui,
                &format!(
                    "  f_m = {:.2} GHz  g\u{2080} = {:.0} kHz  Q = {:.0}",
                    phys.freq_ghz, phys.g0_khz, phys.q_mech
                ),
            );
        }

        section_heading(ui, "DOPPLER COOLING");
        dim_label(ui, "Laser cooling of CNT mechanical mode.");

        ui.add_space(4.0);
        ui.label("Temperature (K)");
        dim_label(ui, "Bath temperature. Lower = fewer thermal phonons.");
        changed |= ui
            .add(
                egui::Slider::new(&mut self.cnt_params.temperature, 0.01..=300.0).logarithmic(true),
            )
            .changed();

        ui.add_space(2.0);
        ui.label("Laser Power (mW)");
        dim_label(
            ui,
            "Drives intracavity photon number \u{2192} cooperativity.",
        );
        changed |= ui
            .add(egui::Slider::new(&mut self.cnt_params.laser_power, 0.1..=50.0).logarithmic(true))
            .changed();

        ui.add_space(2.0);
        ui.label("Detuning (\u{00d7}\u{03c9}_m)");
        dim_label(ui, "Red detuning (-1 = optimal sideband cooling).");
        changed |= ui
            .add(egui::Slider::new(&mut self.cnt_params.detuning, -3.0..=0.0))
            .changed();

        ui.add_space(2.0);
        ui.label("\u{03ba}/2 (\u{00d7}\u{03c9}_m)");
        dim_label(ui, "Cavity half-linewidth.");
        changed |= ui
            .add(egui::Slider::new(&mut self.cnt_params.kappa, 0.01..=2.0).logarithmic(true))
            .changed();

        ui.add_space(2.0);
        ui.label("Piezo Voltage (V)");
        dim_label(ui, "Piezoelectric drive near mechanical resonance.");
        changed |= ui
            .add(egui::Slider::new(
                &mut self.cnt_params.piezo_voltage,
                0.0..=10.0,
            ))
            .changed();

        section_heading(ui, "TONNETZ COHERENCE FILTER");
        dim_label(ui, "Toroidal topology suppresses dephasing noise.");
        ui.add_space(4.0);
        ui.label("Grid Size (N)");
        dim_label(
            ui,
            "N\u{00d7}N Tonnetz torus. Larger \u{2192} stronger suppression.",
        );
        changed |= ui
            .add(egui::Slider::new(
                &mut self.cnt_params.tonnetz_grid_size,
                3..=16,
            ))
            .changed();
        ui.add_space(2.0);
        ui.label("Q Factor");
        dim_label(ui, "Quality factor. Higher = more enhancement.");
        changed |= ui
            .add(egui::Slider::new(&mut self.cnt_params.tonnetz_q, 1.0..=200.0).logarithmic(true))
            .changed();

        section_heading(ui, "LOGICAL LAYER: Toric Code");
        dim_label(ui, "Kitaev toric code + greedy decoder.");
        ui.add_space(4.0);
        ui.label("Lattice N");
        dim_label(ui, "N\u{00d7}N torus with 2N\u{00b2} physical qubits.");
        changed |= ui
            .add(egui::Slider::new(&mut self.cnt_lattice_n, 3..=12))
            .changed();
        ui.add_space(2.0);
        ui.label("MC Trials");
        dim_label(ui, "Monte Carlo error-correction trials.");
        changed |= ui
            .add(egui::Slider::new(&mut self.cnt_mc_trials, 50..=5000).logarithmic(true))
            .changed();
        ui.add_space(2.0);
        ui.label("Gate Time (ns)");
        dim_label(ui, "p = gate_time / T\u{2082}");
        changed |= ui
            .add(egui::Slider::new(&mut self.cnt_gate_time_ns, 10.0..=1000.0).logarithmic(true))
            .changed();

        if changed {
            self.needs_cnt_eval = true;
            self.needs_cnt_sweep = true;
        }
        if self.needs_cnt_eval {
            self.send_cnt_eval();
        }
        if self.needs_cnt_sweep && !self.cnt_sweep_pending {
            self.send_cnt_sweep();
        }

        ui.add_space(6.0);
        ui.separator();
        dim_label(ui, "PIPELINE:");
        dim_label(ui, "  Temp,Laser \u{2192} Doppler \u{2192} n_final");
        dim_label(
            ui,
            "  Tonnetz(\u{03bb}\u{2081},Q) \u{2192} T\u{2082} enhancement",
        );
        dim_label(ui, "  T\u{2082} \u{2192} p = t_gate/T\u{2082}");
        dim_label(ui, "  p \u{2192} Toric code MC \u{2192} P_L");
    }

    fn draw_cnt_results(&self, ui: &mut egui::Ui) {
        let heading = self
            .cnt_physics_result
            .as_ref()
            .map(|p| p.resonator_label)
            .unwrap_or("CNT RESONATOR");
        section_heading(ui, heading);

        if let Some(ref phys) = self.cnt_physics_result {
            ui.label(format!("f_m: {:.2} GHz", phys.freq_ghz));
            dim_label(ui, "  Mechanical frequency");
            ui.label(format!("g\u{2080}: {:.0} kHz", phys.g0_khz));
            dim_label(ui, "  Optomechanical coupling");
            let qc = if phys.q_mech > 1e5 {
                FOREST_GREEN
            } else {
                GOLD_EG
            };
            ui.colored_label(qc, format!("Q: {:.0}", phys.q_mech));
            dim_label(ui, "  Mechanical quality factor");
            ui.label(format!("\u{0394}\u{03c9}: {:.2}", phys.mech_spectral_gap));
            dim_label(
                ui,
                "  Mechanical spectral gap (\u{03c9}\u{2083}/\u{03c9}\u{2082})",
            );
            if phys.resonator_label == "NANOTORUS" {
                dim_label(
                    ui,
                    "  T\u{00b2} modes: winding numbers (m,n). Q enhanced by",
                );
                dim_label(ui, "  elimination of clamping losses.");
            }

            ui.add_space(6.0);
            section_heading(ui, "COOLING");
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
            let enh_c = if phys.tonnetz_enhancement > 5.0 {
                FOREST_GREEN
            } else {
                GOLD_EG
            };
            ui.colored_label(
                enh_c,
                format!("Enhancement: {:.1}\u{00d7}", phys.tonnetz_enhancement),
            );
            dim_label(ui, "  Dephasing suppression factor");

            ui.add_space(6.0);
            section_heading(ui, "COHERENCE TIMES");
            ui.label(format!("T\u{2081}: {:.0} ns", phys.t1_ns));
            dim_label(ui, "  Relaxation time");
            let t2c = if phys.t2_ns > self.cnt_gate_time_ns * 10.0 {
                FOREST_GREEN
            } else {
                WARN_RED
            };
            ui.colored_label(
                t2c,
                format!("T\u{2082}: {:.0} ns  (with Tonnetz)", phys.t2_ns),
            );
            dim_label(ui, "  Phase coherence time");
            ui.label(format!("T\u{2082} bare: {:.0} ns", phys.t2_bare_ns));
            let imp = phys.t2_ns - phys.t2_bare_ns;
            let imp_c = if imp > 100.0 { FOREST_GREEN } else { GOLD_EG };
            ui.colored_label(
                imp_c,
                format!("\u{0394}T\u{2082}: +{:.0} ns improvement", imp),
            );
        }

        ui.add_space(6.0);
        section_heading(ui, "ERROR CORRECTION");
        ui.label(format!("p = {:.4}", self.cnt_p_error));
        dim_label(ui, "  Physical error rate");
        let margin = 0.09 - self.cnt_p_error;
        let mc = if margin > 0.0 { FOREST_GREEN } else { WARN_RED };
        ui.colored_label(mc, format!("Margin: {:.1}%", margin * 100.0));
        if margin > 0.0 {
            dim_label(ui, "  BELOW threshold \u{2713}");
        } else {
            ui.colored_label(WARN_RED, "  ABOVE threshold!");
        }
        ui.label(format!(
            "P_L = {:.3}  ({}/{})",
            self.cnt_logical_error_rate, self.cnt_logical_failures, self.cnt_mc_trials_done
        ));
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
        if torus_response.double_clicked() {
            self.auto_rotate = true;
        }
        if torus_response.hovered() {
            torus_response.on_hover_text("Drag to rotate | Double-click to reset");
        }

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
        let tooltip_text = if let (Some((row, col)), Some(ref snap)) =
            (self.cnt_hovered_node, &self.cnt_snapshot)
        {
            let n = snap.n;
            let hi = row * n + col;
            let vi = n * n + row * n + col;
            let hx = snap.x_errors.get(hi).copied().unwrap_or(false);
            let hz = snap.z_errors.get(hi).copied().unwrap_or(false);
            let vx = snap.x_errors.get(vi).copied().unwrap_or(false);
            let vz = snap.z_errors.get(vi).copied().unwrap_or(false);
            let is_e = snap.e_particles.contains(&(row, col));
            let is_m = snap.m_particles.contains(&(row, col));
            Some(format!(
                "Vertex ({}, {})\nH-edge: X={} Z={}\nV-edge: X={} Z={}\n{}{}",
                row,
                col,
                if hx { "err" } else { "ok" },
                if hz { "err" } else { "ok" },
                if vx { "err" } else { "ok" },
                if vz { "err" } else { "ok" },
                if is_e { "e-particle " } else { "" },
                if is_m { "m-particle" } else { "" }
            ))
        } else {
            None
        };
        if let Some(tip) = tooltip_text {
            lat_response.clone().on_hover_text(tip);
        }

        // Left-click toggle
        if lat_response.clicked() {
            if let Some((row, col)) = self.cnt_hovered_node {
                if let Some(ref mut snap) = self.cnt_snapshot {
                    let hi = row * snap.n + col;
                    if let Some(v) = snap.x_errors.get_mut(hi) {
                        *v = !*v;
                    }
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
                        if let Some(v) = snap.x_errors.get_mut(hi) {
                            *v = !*v;
                        }
                        let (e, m) = cnt_bridge::recompute_syndromes(snap);
                        snap.e_particles = e;
                        snap.m_particles = m;
                    }
                    ui.close_menu();
                }
                if ui.button("Toggle Z error (H-edge)").clicked() {
                    if let Some(ref mut snap) = self.cnt_snapshot {
                        let hi = row * snap.n + col;
                        if let Some(v) = snap.z_errors.get_mut(hi) {
                            *v = !*v;
                        }
                        let (e, m) = cnt_bridge::recompute_syndromes(snap);
                        snap.e_particles = e;
                        snap.m_particles = m;
                    }
                    ui.close_menu();
                }
                if ui.button("Toggle X error (V-edge)").clicked() {
                    if let Some(ref mut snap) = self.cnt_snapshot {
                        let vi = snap.n * snap.n + row * snap.n + col;
                        if let Some(v) = snap.x_errors.get_mut(vi) {
                            *v = !*v;
                        }
                        let (e, m) = cnt_bridge::recompute_syndromes(snap);
                        snap.e_particles = e;
                        snap.m_particles = m;
                    }
                    ui.close_menu();
                }
                if ui.button("Toggle Z error (V-edge)").clicked() {
                    if let Some(ref mut snap) = self.cnt_snapshot {
                        let vi = snap.n * snap.n + row * snap.n + col;
                        if let Some(v) = snap.z_errors.get_mut(vi) {
                            *v = !*v;
                        }
                        let (e, m) = cnt_bridge::recompute_syndromes(snap);
                        snap.e_particles = e;
                        snap.m_particles = m;
                    }
                    ui.close_menu();
                }
            } else {
                ui.label("No vertex selected");
            }
        });

        // Drawing
        let painter = ui.painter();

        painter.text(
            torus_rect.center_top() + egui::vec2(0.0, 12.0),
            egui::Align2::CENTER_TOP,
            format!(
                "3D TORUS (T\u{00b2})  \u{2014}  Tonnetz {0}\u{00d7}{0}",
                self.cnt_params.tonnetz_grid_size
            ),
            egui::FontId::proportional(13.0),
            HEADING_CLR,
        );
        painter.text(
            lat_rect.center_top() + egui::vec2(0.0, 12.0),
            egui::Align2::CENTER_TOP,
            format!(
                "{0}\u{00d7}{0} TORIC CODE  \u{2014}  Pauli frame snapshot",
                self.cnt_lattice_n
            ),
            egui::FontId::proportional(13.0),
            HEADING_CLR,
        );

        draw_cnt_torus(
            painter,
            torus_rect,
            self.rotation,
            self.cnt_params.tonnetz_grid_size,
            self.cnt_snapshot.as_ref(),
            self.time,
        );
        if let Some(ref snap) = self.cnt_snapshot {
            draw_lattice(painter, lat_rect, snap, self.cnt_hovered_node);
        }

        // Threshold chart
        painter.text(
            bot.center_top() + egui::vec2(0.0, 4.0),
            egui::Align2::CENTER_TOP,
            "THRESHOLD CURVE  \u{2014}  physical error rate p vs logical error rate P_L",
            egui::FontId::proportional(12.0),
            HEADING_CLR,
        );

        let chart_inner = egui::Rect::from_min_max(
            bot.min + egui::vec2(10.0, 22.0),
            bot.max - egui::vec2(10.0, 5.0),
        );
        let p_error = self.cnt_p_error;
        let logical_error_rate = self.cnt_logical_error_rate;

        ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart_inner), |ui| {
            let plot = Plot::new("cnt_threshold_chart")
                .width(chart_inner.width())
                .height(chart_inner.height())
                .x_axis_label("p (physical error rate)")
                .y_axis_label("P_L")
                .include_x(0.0)
                .include_x(0.2)
                .include_y(0.0)
                .include_y(1.0)
                .show_axes(true)
                .allow_zoom(true)
                .allow_drag(true)
                .allow_scroll(true)
                .legend(Legend::default().position(Corner::LeftTop))
                .label_formatter(move |name, value| {
                    if !name.is_empty() {
                        format!("{}\np = {:.4}\nP_L = {:.4}", name, value.x, value.y)
                    } else {
                        format!("p = {:.4}\nP_L = {:.4}", value.x, value.y)
                    }
                });

            plot.show(ui, |plot_ui| {
                // Correctable zone
                let zone_pts: PlotPoints = vec![[0.0, 0.0], [0.09, 0.0], [0.09, 1.0], [0.0, 1.0]]
                    .into_iter()
                    .collect();
                plot_ui.polygon(
                    Polygon::new(zone_pts)
                        .fill_color(egui::Color32::from_rgba_unmultiplied(86, 166, 96, 20))
                        .stroke(egui::Stroke::NONE)
                        .name("Correctable zone"),
                );

                let colors = [
                    FOREST_GREEN,
                    GOLD_EG,
                    egui::Color32::from_rgb(200, 200, 190),
                    X_ERROR_RED,
                ];
                let markers = [
                    MarkerShape::Circle,
                    MarkerShape::Diamond,
                    MarkerShape::Square,
                    MarkerShape::Up,
                ];

                if let Some(ref cd) = self.cnt_chart_data {
                    for (i, curve) in cd.curves.iter().enumerate() {
                        let pts: PlotPoints = curve.points.iter().map(|&(p, pl)| [p, pl]).collect();
                        let scatter_pts: PlotPoints =
                            curve.points.iter().map(|&(p, pl)| [p, pl]).collect();
                        let color = colors[i % colors.len()];
                        let marker = markers[i % markers.len()];
                        let name = format!("N={}", curve.n);
                        plot_ui.line(Line::new(pts).color(color).width(2.0).name(&name));
                        plot_ui.points(
                            Points::new(scatter_pts)
                                .color(color)
                                .shape(marker)
                                .radius(3.5)
                                .name(&name),
                        );
                    }
                }

                if p_error > 0.0 {
                    plot_ui.vline(
                        VLine::new(p_error)
                            .color(egui::Color32::WHITE)
                            .width(1.5)
                            .name("Operating point"),
                    );
                    plot_ui.text(
                        PlotText::new(
                            PlotPoint::new(p_error, logical_error_rate.max(0.05)),
                            egui::RichText::new(format!("p={:.4}", p_error))
                                .size(10.0)
                                .color(egui::Color32::WHITE),
                        )
                        .anchor(egui::Align2::LEFT_BOTTOM),
                    );
                }
                plot_ui.vline(
                    VLine::new(0.09)
                        .color(egui::Color32::from_rgba_unmultiplied(230, 70, 70, 120))
                        .width(1.0)
                        .name("Threshold ~9%"),
                );
                plot_ui.text(
                    PlotText::new(
                        PlotPoint::new(0.092, 0.92),
                        egui::RichText::new("p_th ~ 9%")
                            .size(10.0)
                            .color(X_ERROR_RED),
                    )
                    .anchor(egui::Align2::LEFT_TOP),
                );
            });
        });

        let _ = ctx; // used for context menu
    }

    fn draw_cnt_status(&self, ctx: &egui::Context) {
        if let Some(ref phys) = self.cnt_physics_result {
            // Primary: error correctability
            let (st, sc) = if self.cnt_p_error < 0.09 {
                ("CORRECTABLE", FOREST_GREEN)
            } else {
                ("TOO NOISY", WARN_RED)
            };
            // Secondary: coherence — must check absolute T₂, not just enhancement factor
            let (coh_st, coh_sc) = if phys.t2_ns < 1.0 {
                ("NEGLIGIBLE", WARN_RED)
            } else if phys.tonnetz_enhancement > 5.0 && phys.t2_ns > self.cnt_gate_time_ns {
                ("EFFECTIVE", FOREST_GREEN)
            } else if phys.tonnetz_enhancement > 1.5 {
                ("MODERATE", GOLD_EG)
            } else {
                ("MARGINAL", WARN_RED)
            };
            let frame = egui::Frame {
                fill: egui::Color32::from_rgba_unmultiplied(22, 28, 22, 230),
                corner_radius: egui::CornerRadius::from(6),
                inner_margin: egui::Margin::same(10),
                stroke: egui::Stroke::new(2.0, sc),
                ..Default::default()
            };
            egui::Window::new("cnt_status")
                .title_bar(false)
                .resizable(false)
                .movable(false)
                .frame(frame)
                .anchor(egui::Align2::RIGHT_BOTTOM, [-10.0, -10.0])
                .show(ctx, |ui| {
                    ui.horizontal(|ui| {
                        ui.colored_label(sc, egui::RichText::new(st).strong().size(15.0));
                        ui.separator();
                        ui.colored_label(
                            coh_sc,
                            egui::RichText::new(format!("Coherence {}", coh_st))
                                .strong()
                                .size(13.0),
                        );
                    });
                    ui.label(format!(
                        "T\u{2082}={:.0}ns  p={:.4}  P_L={:.3}",
                        phys.t2_ns, self.cnt_p_error, self.cnt_logical_error_rate
                    ));
                    dim_label(
                        ui,
                        &format!(
                            "{}: +{:.0}ns ({:.0}\u{00d7})",
                            phys.resonator_label,
                            phys.t2_ns - phys.t2_bare_ns,
                            phys.tonnetz_enhancement
                        ),
                    );
                    if self.paused {
                        ui.colored_label(GOLD_EG, egui::RichText::new("PAUSED").size(11.0));
                    }
                });
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Hallucination Reduction tab methods
// ═══════════════════════════════════════════════════════════════════════════════

impl QuantumEngineApp {
    fn draw_drift_controls(&mut self, ui: &mut egui::Ui) {
        ui.colored_label(
            GOLD_EG,
            egui::RichText::new("HALLUCINATION REDUCTION")
                .strong()
                .size(13.0),
        );
        dim_label(ui, "Toroidal logit bias on T\u{00b2}");
        ui.add_space(4.0);

        let mut changed = false;

        // ── Tonnetz Parameters ──
        section_heading(ui, "TONNETZ PARAMETERS");

        ui.label("Grid Size N");
        let mut n_f = self.drift_config.grid_n as f64;
        if ui
            .add(
                egui::Slider::new(&mut n_f, 4.0..=24.0)
                    .step_by(1.0)
                    .suffix(""),
            )
            .changed()
        {
            self.drift_config.grid_n = n_f as usize;
            changed = true;
        }

        ui.label("Walk Steps");
        let mut steps_f = self.drift_config.num_steps as f64;
        if ui
            .add(
                egui::Slider::new(&mut steps_f, 100.0..=5000.0)
                    .logarithmic(true)
                    .suffix(""),
            )
            .changed()
        {
            self.drift_config.num_steps = steps_f as usize;
            changed = true;
        }

        // ── Attention Mask ──
        section_heading(ui, "ATTENTION MASK");

        ui.label("Mask Type");
        ui.horizontal(|ui| {
            if ui
                .selectable_label(self.drift_config.mask_type == MaskType::HardCutoff, "Hard")
                .clicked()
            {
                self.drift_config.mask_type = MaskType::HardCutoff;
                changed = true;
            }
            if ui
                .selectable_label(
                    self.drift_config.mask_type == MaskType::SoftExponential,
                    "Soft",
                )
                .clicked()
            {
                self.drift_config.mask_type = MaskType::SoftExponential;
                changed = true;
            }
            if ui
                .selectable_label(self.drift_config.mask_type == MaskType::Hybrid, "Hybrid")
                .clicked()
            {
                self.drift_config.mask_type = MaskType::Hybrid;
                changed = true;
            }
        });

        ui.label("Radius r");
        if ui
            .add(egui::Slider::new(&mut self.drift_config.radius, 1.0..=8.0).step_by(0.5))
            .changed()
        {
            changed = true;
        }

        ui.label("Decay \u{03b1}");
        if ui
            .add(egui::Slider::new(&mut self.drift_config.alpha, 0.1..=2.0).step_by(0.1))
            .changed()
        {
            changed = true;
        }

        // ── Drift Metric ──
        section_heading(ui, "DRIFT METRIC");

        ui.label("Drift Threshold");
        let mut thresh_f = self.drift_config.drift_threshold as f64;
        if ui
            .add(egui::Slider::new(&mut thresh_f, 1.0..=8.0).step_by(1.0))
            .changed()
        {
            self.drift_config.drift_threshold = thresh_f as usize;
            changed = true;
        }

        // ── Visualization Mode ──
        section_heading(ui, "VISUALIZATION");
        ui.horizontal(|ui| {
            if ui
                .selectable_label(self.drift_viz_mode == DriftVizMode::Overview, "Overview")
                .clicked()
            {
                self.drift_viz_mode = DriftVizMode::Overview;
            }
            if ui
                .selectable_label(self.drift_viz_mode == DriftVizMode::DriftAnalysis, "Drift")
                .clicked()
            {
                self.drift_viz_mode = DriftVizMode::DriftAnalysis;
                if self.needs_drift_analysis { /* will fire in update */ }
            }
            if ui
                .selectable_label(self.drift_viz_mode == DriftVizMode::MaskAnalysis, "Mask")
                .clicked()
            {
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

        // ── Covariant Descent ──
        section_heading(ui, "COVARIANT DESCENT");
        dim_label(ui, "Optimize mask (r, \u{03b1}) on T\u{00b2}.");
        let mut descent_changed = false;

        ui.add_space(4.0);
        ui.label("Learning rate \u{03b7}");
        descent_changed |= ui
            .add(egui::Slider::new(&mut self.drift_descent_eta, 0.0001..=0.05).logarithmic(true))
            .changed();
        ui.add_space(2.0);
        ui.label("Start x (radius)");
        descent_changed |= ui
            .add(egui::Slider::new(
                &mut self.drift_descent_start.0,
                0.0..=1.0,
            ))
            .changed();
        ui.add_space(2.0);
        ui.label("Start y (alpha)");
        descent_changed |= ui
            .add(egui::Slider::new(
                &mut self.drift_descent_start.1,
                0.0..=1.0,
            ))
            .changed();
        ui.add_space(2.0);
        ui.checkbox(&mut self.drift_show_descent_euc, "Show Euclidean path");

        if descent_changed {
            self.needs_drift_descent = true;
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
            let rf_color = if dr.reduction_factor > 1.5 {
                FOREST_GREEN
            } else {
                GOLD_EG
            };
            ui.colored_label(
                rf_color,
                egui::RichText::new(format!("Reduction: {:.1}\u{00d7}", dr.reduction_factor))
                    .strong(),
            );
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

        // ── Quantum Advantage ──
        section_heading(ui, "QUANTUM ADVANTAGE");
        let n_sq = self.drift_config.grid_n * self.drift_config.grid_n;
        let gap_t = crate::coherence::spectral_gap(crate::coherence::Topology::Toroidal, n_sq);
        let gap_l = crate::coherence::spectral_gap(crate::coherence::Topology::Linear, n_sq);
        let advantage = gap_t / gap_l;
        ui.colored_label(
            FOREST_GREEN,
            format!("T\u{00b2} / chain: {:.1}\u{00d7}", advantage),
        );
        dim_label(ui, "Toroidal topology protects coherence");
        dim_label(ui, &format!("{} qubits on T\u{00b2} vs linear chain", n_sq));

        // ── Mask Info ──
        section_heading(ui, "MASK CONFIG");
        let mask_name = match self.drift_config.mask_type {
            MaskType::HardCutoff => "Hard Cutoff",
            MaskType::SoftExponential => "Soft Exponential",
            MaskType::Hybrid => "Hybrid",
        };
        ui.label(format!("Type: {}", mask_name));
        ui.label(format!(
            "r = {:.1}, \u{03b1} = {:.1}",
            self.drift_config.radius, self.drift_config.alpha
        ));

        // ── Descent Results ──
        if self.drift_descent_cov.is_some() || self.drift_descent_euc.is_some() {
            section_heading(ui, "DESCENT");
            if let Some(ref cov) = self.drift_descent_cov {
                let conv_str = match cov.convergence_step {
                    Some(s) => format!("step {}", s),
                    None => "running".to_string(),
                };
                ui.colored_label(FOREST_GREEN, "Covariant (T\u{00b2}):");
                ui.label(format!("  Loss: {:.4}", cov.final_loss));
                ui.label(format!("  Conv: {}", conv_str));
                ui.label(format!("  Rate: {:.4}", cov.measured_rate));
                // Decode optimized r and alpha
                if let Some(last) = cov.steps.last() {
                    let opt_r = crate::covariant::denorm_linear(last.position.x, 1.0, 8.0);
                    let opt_a = crate::covariant::denorm_linear(last.position.y, 0.1, 2.0);
                    dim_label(ui, &format!("  Opt: r={:.1} \u{03b1}={:.2}", opt_r, opt_a));
                }
            }
            if let Some(ref euc) = self.drift_descent_euc {
                ui.colored_label(WARN_RED, "Euclidean (flat):");
                ui.label(format!("  Loss: {:.4}", euc.final_loss));
            }
        }

        // ── Benchmark ──
        section_heading(ui, "TRUTHFULQA BENCHMARK");
        dim_label(ui, "Published results (817 samples):");
        ui.add_space(2.0);
        for entry in logit_drift::benchmark_data() {
            ui.horizontal(|ui| {
                let color = if entry.delta_pp >= 2.0 {
                    FOREST_GREEN
                } else {
                    LABEL_CLR
                };
                ui.colored_label(
                    color,
                    egui::RichText::new(format!("+{:.1}pp", entry.delta_pp))
                        .strong()
                        .size(12.0),
                );
                ui.label(egui::RichText::new(entry.model).size(11.0));
            });
        }
    }

    fn draw_drift_central(&mut self, ui: &mut egui::Ui) {
        let total_rect = ui.available_rect_before_wrap();
        let top_h = total_rect.height() * 0.55;
        let bottom_h = total_rect.height() - top_h;

        // ═══ TOP: 3D torus with drift trajectories ═══
        let torus_rect =
            egui::Rect::from_min_size(total_rect.min, egui::vec2(total_rect.width(), top_h));
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

        // Overlay descent paths on drift torus
        {
            let rm = 1.0f32;
            let rn = 0.45f32;
            if let Some(ref cov) = self.drift_descent_cov {
                draw_descent_path(
                    &painter,
                    torus_rect,
                    self.rotation,
                    rm,
                    rn,
                    &cov.steps,
                    true,
                    self.time,
                );
            }
            if self.drift_show_descent_euc {
                if let Some(ref euc) = self.drift_descent_euc {
                    draw_descent_path(
                        &painter,
                        torus_rect,
                        self.rotation,
                        rm,
                        rn,
                        &euc.steps,
                        false,
                        self.time,
                    );
                }
            }
        }

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
                if cross < 0.0 {
                    continue;
                }

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
                painter.line_segment(
                    [a, b],
                    egui::Stroke::new(
                        0.5,
                        egui::Color32::from_rgba_unmultiplied(60, 125, 85, al / 2),
                    ),
                );
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
                painter.line_segment(
                    [a, b],
                    egui::Stroke::new(
                        0.5,
                        egui::Color32::from_rgba_unmultiplied(60, 125, 85, al / 2),
                    ),
                );
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
                painter.line_segment(
                    [a, b],
                    egui::Stroke::new(1.5, egui::Color32::from_rgba_unmultiplied(212, 175, 55, al)),
                );
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
                painter.line_segment(
                    [a, b],
                    egui::Stroke::new(1.5, egui::Color32::from_rgba_unmultiplied(212, 175, 55, al)),
                );
            }
        }

        // (2,3) torus knot — topological protection path
        draw_torus_knot(painter, rect, rot, r_maj, r_min, 2, 3, time, KNOT_CYAN, 1.5);

        // Draw drift trajectories on the torus surface
        if let Some(dr) = drift_result {
            // Toroidal path — green
            Self::draw_path_on_torus(
                painter,
                rect,
                rot,
                r_maj,
                r_min,
                &dr.toroidal_path,
                egui::Color32::from_rgb(100, 230, 120),
                2.0,
            );
            // Baseline path — red
            Self::draw_path_on_torus(
                painter,
                rect,
                rot,
                r_maj,
                r_min,
                &dr.baseline_path,
                egui::Color32::from_rgb(230, 80, 80),
                1.5,
            );
        }

        // Title
        let title_pos = egui::pos2(rect.center().x, rect.min.y + 14.0);
        painter.text(
            title_pos,
            egui::Align2::CENTER_TOP,
            "Semantic Drift on T\u{00b2}",
            egui::FontId::proportional(13.0),
            HEADING_CLR,
        );

        // Legend
        let legend_y = rect.min.y + 30.0;
        painter.text(
            egui::pos2(rect.min.x + 10.0, legend_y),
            egui::Align2::LEFT_TOP,
            "\u{25cf} Toroidal  \u{25cf} Baseline  \u{25cf} Torus Knot",
            egui::FontId::proportional(11.0),
            DIM,
        );
        // Color dots for legend
        painter.circle_filled(
            egui::pos2(rect.min.x + 12.0, legend_y + 6.0),
            3.0,
            egui::Color32::from_rgb(100, 230, 120),
        );
        painter.circle_filled(
            egui::pos2(rect.min.x + 80.0, legend_y + 6.0),
            3.0,
            egui::Color32::from_rgb(230, 80, 80),
        );
        painter.circle_filled(
            egui::pos2(rect.min.x + 160.0, legend_y + 6.0),
            3.0,
            KNOT_CYAN,
        );
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
        if path.len() < 2 {
            return;
        }
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
        painter.text(
            egui::pos2(rect.center().x, title_y),
            egui::Align2::CENTER_TOP,
            "Mask Heatmap (center ref)",
            egui::FontId::proportional(12.0),
            HEADING_CLR,
        );

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
                    let cell =
                        egui::Rect::from_min_size(egui::pos2(x, y), egui::vec2(cell_w, cell_h));

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
                        painter.rect_stroke(
                            cell,
                            0.0,
                            egui::Stroke::new(2.0, egui::Color32::WHITE),
                            egui::epaint::StrokeKind::Outside,
                        );
                    }
                }
            }
        } else {
            painter.text(
                grid_rect.center(),
                egui::Align2::CENTER_CENTER,
                "Computing...",
                egui::FontId::proportional(12.0),
                DIM,
            );
        }
    }

    fn draw_spectral_decay_chart(&self, ui: &mut egui::Ui) {
        ui.colored_label(
            HEADING_CLR,
            egui::RichText::new("Spectral Decay e^(-\u{03bb}\u{2081}t)").size(12.0),
        );

        let curves = logit_drift::spectral_decay_curves(&[8, 12, 16, 24], 5.0, 100);
        let colors = [
            FOREST_GREEN,
            GOLD_EG,
            egui::Color32::from_rgb(200, 200, 190),
            COMPRESS_BLUE,
        ];

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
        ui.colored_label(
            HEADING_CLR,
            egui::RichText::new("TruthfulQA T&I (pp improvement)").size(12.0),
        );

        let entries = logit_drift::benchmark_data();

        let plot = Plot::new("benchmark_bars")
            .height(ui.available_height() - 20.0)
            .width(ui.available_width())
            .include_y(0.0)
            .include_y(3.5)
            .legend(Legend::default().position(Corner::RightTop));

        plot.show(ui, |plot_ui| {
            let bars: Vec<Bar> = entries
                .iter()
                .enumerate()
                .map(|(i, e)| {
                    let color = if e.delta_pp >= 2.0 {
                        FOREST_GREEN
                    } else {
                        GOLD_EG
                    };
                    Bar::new(i as f64, e.delta_pp as f64)
                        .width(0.6)
                        .fill(color)
                        .name(e.model)
                })
                .collect();
            plot_ui.bar_chart(BarChart::new(bars).name("Improvement (pp)"));
        });
    }

    // ─── 5 new advanced simulation charts ──────────────────────────────────

    fn draw_multi_scale_chart(&self, ui: &mut egui::Ui) {
        ui.colored_label(
            HEADING_CLR,
            egui::RichText::new("Multi-Scale Drift Comparison").size(12.0),
        );

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
                    )
                    .color(GOLD_EG);
                    plot_ui.text(text);
                }
            });
        } else {
            dim_label(ui, "Computing...");
        }
    }

    fn draw_phase_transition_chart(&self, ui: &mut egui::Ui) {
        ui.colored_label(
            HEADING_CLR,
            egui::RichText::new("Phase Transition (Drift vs Radius)").size(12.0),
        );

        if let Some(ref da) = self.drift_analysis {
            let plot = Plot::new("phase_transition")
                .height(ui.available_height() - 20.0)
                .width(ui.available_width())
                .x_axis_label("radius")
                .y_axis_label("drift rate")
                .include_y(0.0);

            let pts: Vec<[f64; 2]> = da
                .phase_transition
                .iter()
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
        ui.colored_label(
            HEADING_CLR,
            egui::RichText::new("Adjacency Loss (Local vs Global)").size(12.0),
        );

        if let Some(ref da) = self.drift_analysis {
            let plot = Plot::new("adjacency_loss")
                .height(ui.available_height() - 20.0)
                .width(ui.available_width())
                .legend(Legend::default().position(Corner::RightTop))
                .x_axis_label("radius")
                .include_y(0.0);

            let pos_pts: Vec<[f64; 2]> = da
                .adjacency
                .iter()
                .map(|e| [e.radius as f64, e.pos_mean_dist as f64])
                .collect();
            let neg_pts: Vec<[f64; 2]> = da
                .adjacency
                .iter()
                .map(|e| [e.radius as f64, e.neg_mean_dist as f64])
                .collect();
            let loss_pts: Vec<[f64; 2]> = da
                .adjacency
                .iter()
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
        ui.colored_label(
            HEADING_CLR,
            egui::RichText::new("Sinkhorn-Knopp Convergence").size(12.0),
        );

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
            let pts: Vec<[f64; 2]> = ma.sinkhorn.points.iter().map(|p| [p[0], p[1]]).collect();

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
                    let conv_y = ma
                        .sinkhorn
                        .points
                        .get(ma.sinkhorn.converged_at.saturating_sub(1))
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
        ui.colored_label(
            HEADING_CLR,
            egui::RichText::new("Sparsity vs Threshold").size(12.0),
        );

        if let Some(ref ma) = self.mask_analysis {
            let plot = Plot::new("sparsity_sweep")
                .height(ui.available_height() - 20.0)
                .width(ui.available_width())
                .legend(Legend::default().position(Corner::RightTop))
                .include_y(0.0)
                .include_y(1.0);

            plot.show(ui, |plot_ui| {
                // Sparsity bars
                let bars: Vec<Bar> = ma
                    .sparsity
                    .iter()
                    .enumerate()
                    .map(|(i, e)| {
                        Bar::new(i as f64, e.sparsity as f64)
                            .width(0.6)
                            .fill(FOREST_GREEN)
                            .name(format!("t={:.3}", e.threshold))
                    })
                    .collect();
                plot_ui.bar_chart(BarChart::new(bars).name("Sparsity"));

                // Memory savings line (normalized to [0,1])
                let max_dense = ma.sparsity.first().map_or(1, |e| e.dense_memory).max(1);
                let mem_pts: Vec<[f64; 2]> = ma
                    .sparsity
                    .iter()
                    .enumerate()
                    .map(|(i, e)| [i as f64, e.memory_bytes as f64 / max_dense as f64])
                    .collect();
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
            let (st, sc) = if dr.reduction_factor > 1.5 {
                ("EFFECTIVE", FOREST_GREEN)
            } else {
                ("MARGINAL", GOLD_EG)
            };
            let frame = egui::Frame {
                fill: egui::Color32::from_rgba_unmultiplied(22, 28, 22, 230),
                corner_radius: egui::CornerRadius::from(6),
                inner_margin: egui::Margin::same(10),
                stroke: egui::Stroke::new(2.0, sc),
                ..Default::default()
            };
            egui::Window::new("drift_status")
                .title_bar(false)
                .resizable(false)
                .movable(false)
                .frame(frame)
                .anchor(egui::Align2::RIGHT_BOTTOM, [-10.0, -10.0])
                .show(ctx, |ui| {
                    ui.colored_label(sc, egui::RichText::new(st).strong().size(15.0));
                    ui.label(format!(
                        "{:.1}\u{00d7} reduction  \u{03bb}\u{2081}={:.4}  drift={:.3}",
                        dr.reduction_factor, dr.spectral_gap, dr.toroidal_drift_rate
                    ));
                    if let Some(ref cov) = self.drift_descent_cov {
                        dim_label(
                            ui,
                            &format!(
                                "Descent: {} steps, loss={:.4}",
                                cov.steps.len(),
                                cov.final_loss
                            ),
                        );
                    }
                    if self.paused {
                        ui.colored_label(GOLD_EG, egui::RichText::new("PAUSED").size(11.0));
                    }
                });
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Nanotorus tab methods
// ═══════════════════════════════════════════════════════════════════════════════

impl QuantumEngineApp {
    fn draw_nano_controls(&mut self, ui: &mut egui::Ui) {
        ui.colored_label(
            TORUS_BLUE,
            egui::RichText::new("NANOTORUS SIMULATOR")
                .strong()
                .size(13.0),
        );
        dim_label(ui, "Nanotorus (T\u{00b2}) resonator physics");
        ui.add_space(4.0);

        section_heading(ui, "PRESETS");
        let mut preset_changed = false;
        ui.horizontal(|ui| {
            if ui
                .add(egui::Button::new(
                    egui::RichText::new("Optimal")
                        .color(FOREST_GREEN)
                        .size(12.0),
                ))
                .clicked()
            {
                self.nano_params = PhysicsParams::nanotorus_default();
                self.nano_lattice_n = 6;
                self.nano_mc_trials = 500;
                self.nano_gate_time_ns = 50.0;
                preset_changed = true;
            }
            if ui
                .add(egui::Button::new(
                    egui::RichText::new("Large Ring")
                        .color(TORUS_BLUE)
                        .size(12.0),
                ))
                .clicked()
            {
                self.nano_params = PhysicsParams::nanotorus_default();
                self.nano_params.ring_diameter_nm = 500.0;
                preset_changed = true;
            }
            if ui
                .add(egui::Button::new(
                    egui::RichText::new("Room Temp").color(WARN_RED).size(12.0),
                ))
                .clicked()
            {
                self.nano_params = PhysicsParams::nanotorus_default();
                self.nano_params.temperature = 300.0;
                self.nano_params.laser_power = 5.0;
                preset_changed = true;
            }
        });
        ui.horizontal(|ui| {
            if ui
                .add(egui::Button::new(
                    egui::RichText::new("Bundle Chain")
                        .color(GOLD_EG)
                        .size(12.0),
                ))
                .clicked()
            {
                self.nano_params = PhysicsParams::nanotorus_default();
                self.nano_params.bundle_geometry = BundleGeometry::Chain { count: 4 };
                self.nano_lattice_n = 6;
                self.nano_mc_trials = 500;
                self.nano_gate_time_ns = 50.0;
                preset_changed = true;
            }
            if ui
                .add(egui::Button::new(
                    egui::RichText::new("BN Torus").color(TORUS_BLUE).size(12.0),
                ))
                .clicked()
            {
                self.nano_params = PhysicsParams::nanotorus_default();
                self.nano_params.material = Material::BoronNitride;
                preset_changed = true;
            }
        });

        section_heading(ui, "MATERIAL");
        let mut changed = preset_changed;
        {
            let prev = self.nano_params.material;
            egui::ComboBox::from_id_salt("nano_material")
                .selected_text(self.nano_params.material.label())
                .show_ui(ui, |ui| {
                    ui.selectable_value(&mut self.nano_params.material, Material::Carbon, "Carbon");
                    ui.selectable_value(
                        &mut self.nano_params.material,
                        Material::BoronNitride,
                        "Boron Nitride",
                    );
                    ui.selectable_value(
                        &mut self.nano_params.material,
                        Material::MoS2,
                        "MoS\u{2082}",
                    );
                    ui.selectable_value(
                        &mut self.nano_params.material,
                        Material::SiliconCarbide,
                        "Silicon Carbide",
                    );
                });
            if self.nano_params.material != prev {
                changed = true;
            }
            let desc = match self.nano_params.material {
                Material::Carbon => "E=1.0 TPa, \u{03c1}=2200 kg/m\u{00b3}",
                Material::BoronNitride => "E=0.8 TPa, \u{03c1}=2100, low charge noise",
                Material::MoS2 => "E=0.27 TPa, \u{03c1}=5060, semiconducting",
                Material::SiliconCarbide => "E=0.45 TPa, \u{03c1}=3210, excellent thermal",
            };
            dim_label(ui, desc);
        }

        section_heading(ui, "BUNDLE GEOMETRY");
        {
            let prev_bundle = self.nano_params.bundle_geometry;
            // Track the selected variant (ignoring inner count)
            let mut sel = match self.nano_params.bundle_geometry {
                BundleGeometry::Single => 0u8,
                BundleGeometry::Chain { .. } => 1,
                BundleGeometry::RingOfRings { .. } => 2,
                BundleGeometry::Concentric { .. } => 3,
                BundleGeometry::HopfLink => 4,
            };
            egui::ComboBox::from_id_salt("nano_bundle")
                .selected_text(self.nano_params.bundle_geometry.label())
                .show_ui(ui, |ui| {
                    ui.selectable_value(&mut sel, 0, "Single");
                    ui.selectable_value(&mut sel, 1, "Chain");
                    ui.selectable_value(&mut sel, 2, "Ring of Rings");
                    ui.selectable_value(&mut sel, 3, "Concentric");
                    ui.selectable_value(&mut sel, 4, "Hopf Link");
                });
            // Convert variant index back to enum, preserving count
            let new_bundle = match sel {
                0 => BundleGeometry::Single,
                1 => {
                    let c = match prev_bundle {
                        BundleGeometry::Chain { count } => count,
                        _ => 4,
                    };
                    BundleGeometry::Chain { count: c }
                }
                2 => {
                    let c = match prev_bundle {
                        BundleGeometry::RingOfRings { count } => count,
                        _ => 4,
                    };
                    BundleGeometry::RingOfRings { count: c }
                }
                3 => {
                    let c = match prev_bundle {
                        BundleGeometry::Concentric { layers } => layers,
                        _ => 3,
                    };
                    BundleGeometry::Concentric { layers: c }
                }
                4 => BundleGeometry::HopfLink,
                _ => BundleGeometry::Single,
            };
            self.nano_params.bundle_geometry = new_bundle;
            if self.nano_params.bundle_geometry != prev_bundle {
                changed = true;
            }

            // Count slider for variants that need it
            match &mut self.nano_params.bundle_geometry {
                BundleGeometry::Chain { count } | BundleGeometry::RingOfRings { count } => {
                    ui.add_space(2.0);
                    ui.label("Bundle Count");
                    let mut c = *count as f64;
                    if ui
                        .add(egui::Slider::new(&mut c, 2.0..=8.0).step_by(1.0))
                        .changed()
                    {
                        *count = c as usize;
                        changed = true;
                    }
                }
                BundleGeometry::Concentric { layers } => {
                    ui.add_space(2.0);
                    ui.label("Layers");
                    let mut c = *layers as f64;
                    if ui
                        .add(egui::Slider::new(&mut c, 2.0..=8.0).step_by(1.0))
                        .changed()
                    {
                        *layers = c as usize;
                        changed = true;
                    }
                }
                _ => {}
            }

            let bundle_desc = match self.nano_params.bundle_geometry {
                BundleGeometry::Single => "Single nanotorus",
                BundleGeometry::Chain { .. } => "Linear chain, end-to-end coupling",
                BundleGeometry::RingOfRings { .. } => "Ring of rings (T\u{00b2} of T\u{00b2})",
                BundleGeometry::Concentric { .. } => "Concentric, all-to-all coupling",
                BundleGeometry::HopfLink => "Hopf link: two interlocked tori",
            };
            dim_label(ui, bundle_desc);
            if self.nano_params.bundle_geometry.n_resonators() > 1 {
                dim_label(
                    ui,
                    &format!(
                        "  {} resonators, Q\u{00d7}{:.1}",
                        self.nano_params.bundle_geometry.n_resonators(),
                        self.nano_params.bundle_geometry.cooperative_q_factor()
                    ),
                );
            }
        }

        section_heading(ui, "RING GEOMETRY");

        // Always nanotorus
        self.nano_params.resonator_type = ResonatorType::Nanotorus;

        ui.add_space(4.0);
        ui.label("Ring Diameter (nm)");
        dim_label(
            ui,
            "Major ring diameter. \u{03c9}\u{2082} \u{221d} 1/R\u{00b2}.",
        );
        changed |= ui
            .add(
                egui::Slider::new(&mut self.nano_params.ring_diameter_nm, 50.0..=1000.0)
                    .logarithmic(true),
            )
            .changed();

        ui.add_space(2.0);
        ui.label("Tube Diameter (nm)");
        dim_label(ui, "SWCNT ~1\u{2013}2nm, MWCNT ~5\u{2013}50nm.");
        changed |= ui
            .add(
                egui::Slider::new(&mut self.nano_params.cnt_diameter_nm, 0.5..=50.0)
                    .logarithmic(true),
            )
            .changed();

        ui.add_space(2.0);
        ui.label("Walls");
        dim_label(ui, "1=SWCNT, 2+=MWCNT. More walls \u{2192} lower Q.");
        let mut walls_f = self.nano_params.num_walls as f64;
        if ui
            .add(egui::Slider::new(&mut walls_f, 1.0..=10.0).step_by(1.0))
            .changed()
        {
            self.nano_params.num_walls = walls_f as usize;
            changed = true;
        }

        ui.add_space(2.0);
        ui.label("Cavity Finesse");
        dim_label(ui, "Higher \u{2192} narrower linewidth.");
        changed |= ui
            .add(
                egui::Slider::new(&mut self.nano_params.cavity_finesse, 100.0..=100000.0)
                    .logarithmic(true),
            )
            .changed();

        if let Some(ref phys) = self.nano_physics_result {
            ui.add_space(2.0);
            dim_label(
                ui,
                &format!(
                    "  f_m = {:.2} GHz  g\u{2080} = {:.0} kHz  Q = {:.0}",
                    phys.freq_ghz, phys.g0_khz, phys.q_mech
                ),
            );
        }

        section_heading(ui, "DOPPLER COOLING");
        dim_label(ui, "Laser cooling of nanotorus mechanical mode.");

        ui.add_space(4.0);
        ui.label("Temperature (K)");
        dim_label(ui, "Bath temperature.");
        changed |= ui
            .add(
                egui::Slider::new(&mut self.nano_params.temperature, 0.01..=300.0)
                    .logarithmic(true),
            )
            .changed();

        ui.add_space(2.0);
        ui.label("Laser Power (mW)");
        changed |= ui
            .add(egui::Slider::new(&mut self.nano_params.laser_power, 0.1..=50.0).logarithmic(true))
            .changed();

        ui.add_space(2.0);
        ui.label("Detuning (\u{00d7}\u{03c9}_m)");
        changed |= ui
            .add(egui::Slider::new(
                &mut self.nano_params.detuning,
                -3.0..=0.0,
            ))
            .changed();

        ui.add_space(2.0);
        ui.label("\u{03ba}/2 (\u{00d7}\u{03c9}_m)");
        changed |= ui
            .add(egui::Slider::new(&mut self.nano_params.kappa, 0.01..=2.0).logarithmic(true))
            .changed();

        ui.add_space(2.0);
        ui.label("Piezo Voltage (V)");
        changed |= ui
            .add(egui::Slider::new(
                &mut self.nano_params.piezo_voltage,
                0.0..=10.0,
            ))
            .changed();

        section_heading(ui, "TONNETZ COHERENCE FILTER");
        ui.add_space(4.0);
        ui.label("Grid Size (N)");
        changed |= ui
            .add(egui::Slider::new(
                &mut self.nano_params.tonnetz_grid_size,
                3..=16,
            ))
            .changed();
        ui.add_space(2.0);
        ui.label("Q Factor");
        changed |= ui
            .add(egui::Slider::new(&mut self.nano_params.tonnetz_q, 1.0..=200.0).logarithmic(true))
            .changed();

        section_heading(ui, "TORIC CODE");
        ui.add_space(4.0);
        ui.label("Lattice N");
        changed |= ui
            .add(egui::Slider::new(&mut self.nano_lattice_n, 3..=12))
            .changed();
        ui.add_space(2.0);
        ui.label("MC Trials");
        changed |= ui
            .add(egui::Slider::new(&mut self.nano_mc_trials, 50..=5000).logarithmic(true))
            .changed();
        ui.add_space(2.0);
        ui.label("Gate Time (ns)");
        changed |= ui
            .add(egui::Slider::new(&mut self.nano_gate_time_ns, 10.0..=1000.0).logarithmic(true))
            .changed();

        section_heading(ui, "COVARIANT DESCENT");
        dim_label(ui, "Optimize physics parameters on T\u{00b2}.");
        let mut descent_changed = false;

        ui.add_space(4.0);
        ui.label("Target");
        let prev_target = self.nano_descent_target;
        egui::ComboBox::from_id_salt("nano_descent_target")
            .selected_text(match self.nano_descent_target {
                NanoDescentTarget::RingGeometry => "Ring Geometry",
                NanoDescentTarget::TonnetzFilter => "Tonnetz Filter",
                NanoDescentTarget::Cooling => "Cooling",
            })
            .show_ui(ui, |ui| {
                ui.selectable_value(
                    &mut self.nano_descent_target,
                    NanoDescentTarget::RingGeometry,
                    "Ring Geometry",
                );
                ui.selectable_value(
                    &mut self.nano_descent_target,
                    NanoDescentTarget::TonnetzFilter,
                    "Tonnetz Filter",
                );
                ui.selectable_value(
                    &mut self.nano_descent_target,
                    NanoDescentTarget::Cooling,
                    "Cooling",
                );
            });
        if self.nano_descent_target != prev_target {
            descent_changed = true;
        }

        ui.add_space(2.0);
        ui.label("Learning rate \u{03b7}");
        descent_changed |= ui
            .add(egui::Slider::new(&mut self.nano_descent_eta, 0.0001..=0.05).logarithmic(true))
            .changed();
        ui.add_space(2.0);
        ui.label("Start x");
        descent_changed |= ui
            .add(egui::Slider::new(&mut self.nano_descent_start.0, 0.0..=1.0))
            .changed();
        ui.add_space(2.0);
        ui.label("Start y");
        descent_changed |= ui
            .add(egui::Slider::new(&mut self.nano_descent_start.1, 0.0..=1.0))
            .changed();
        ui.add_space(2.0);
        ui.checkbox(&mut self.nano_show_euclidean, "Show Euclidean path");

        if changed {
            self.needs_nano_eval = true;
            self.needs_nano_sweep = true;
        }
        if descent_changed {
            self.needs_nano_descent = true;
        }
        if self.needs_nano_eval {
            self.send_nano_eval();
        }
        if self.needs_nano_sweep && !self.nano_sweep_pending {
            self.send_nano_sweep();
        }
        if self.needs_nano_descent {
            self.send_nano_descent();
        }
    }

    fn draw_nano_results(&self, ui: &mut egui::Ui) {
        let mat_label = self.nano_params.material.label();
        let bundle_label = self.nano_params.bundle_geometry.label();
        let heading = if self.nano_params.bundle_geometry.n_resonators() > 1 {
            format!("NANOTORUS ({} {})", mat_label, bundle_label)
        } else {
            format!("NANOTORUS ({})", mat_label)
        };
        section_heading(ui, &heading);

        if let Some(ref phys) = self.nano_physics_result {
            ui.label(format!("f_m: {:.2} GHz", phys.freq_ghz));
            dim_label(ui, "  Mechanical frequency");
            ui.label(format!("g\u{2080}: {:.0} kHz", phys.g0_khz));
            dim_label(ui, "  Optomechanical coupling (WGM)");
            let qc = if phys.q_mech > 1e6 {
                FOREST_GREEN
            } else {
                GOLD_EG
            };
            ui.colored_label(qc, format!("Q: {:.0}", phys.q_mech));
            dim_label(ui, "  No clamping losses");
            if self.nano_params.bundle_geometry.n_resonators() > 1 {
                dim_label(
                    ui,
                    &format!(
                        "  Bundle: {} tori, mass {:.1}\u{00d7}, Q\u{00d7}{:.1}",
                        self.nano_params.bundle_geometry.n_resonators(),
                        self.nano_params.bundle_geometry.mass_factor(),
                        self.nano_params.bundle_geometry.cooperative_q_factor()
                    ),
                );
            }
            ui.label(format!("\u{0394}\u{03c9}: {:.2}", phys.mech_spectral_gap));
            dim_label(
                ui,
                "  Mechanical spectral gap (\u{03c9}\u{2083}/\u{03c9}\u{2082})",
            );
            dim_label(ui, "  T\u{00b2} modes: winding numbers (m,n)");

            ui.add_space(6.0);
            section_heading(ui, "COOLING");
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
            let enh_c = if phys.tonnetz_enhancement > 5.0 {
                FOREST_GREEN
            } else {
                GOLD_EG
            };
            ui.colored_label(
                enh_c,
                format!("Enhancement: {:.1}\u{00d7}", phys.tonnetz_enhancement),
            );

            ui.add_space(6.0);
            section_heading(ui, "COHERENCE TIMES");
            ui.label(format!("T\u{2081}: {:.0} ns", phys.t1_ns));
            let t2c = if phys.t2_ns > self.nano_gate_time_ns * 10.0 {
                FOREST_GREEN
            } else {
                WARN_RED
            };
            ui.colored_label(
                t2c,
                format!("T\u{2082}: {:.0} ns  (with Tonnetz)", phys.t2_ns),
            );
            ui.label(format!("T\u{2082} bare: {:.0} ns", phys.t2_bare_ns));
            let imp = phys.t2_ns - phys.t2_bare_ns;
            let imp_c = if imp > 100.0 { FOREST_GREEN } else { GOLD_EG };
            ui.colored_label(imp_c, format!("\u{0394}T\u{2082}: +{:.0} ns", imp));

            // Quantum advantage summary
            ui.add_space(6.0);
            section_heading(ui, "QUANTUM ADVANTAGE");

            let n_qubits =
                (self.nano_params.tonnetz_grid_size * self.nano_params.tonnetz_grid_size) as usize;
            let gap_torus =
                crate::coherence::spectral_gap(crate::coherence::Topology::Toroidal, n_qubits);
            let gap_linear =
                crate::coherence::spectral_gap(crate::coherence::Topology::Linear, n_qubits);
            let topo_advantage = gap_torus / gap_linear;

            ui.colored_label(
                FOREST_GREEN,
                format!("T\u{00b2} advantage: {:.1}\u{00d7}", topo_advantage),
            );
            dim_label(
                ui,
                &format!(
                    "  \u{03bb}\u{2081}(T\u{00b2})={:.4} vs \u{03bb}\u{2081}(chain)={:.4}",
                    gap_torus, gap_linear
                ),
            );

            // Gate error threshold
            let p_gate = self.nano_gate_time_ns / phys.t2_ns;
            let viable = p_gate < 0.01;
            let tc = if viable { FOREST_GREEN } else { WARN_RED };
            ui.colored_label(tc, format!("Gate error: {:.2e}", p_gate));
            if viable {
                dim_label(ui, "  BELOW 1% toric code threshold");
            } else {
                ui.colored_label(WARN_RED, "  ABOVE threshold");
            }

            // Physical coherence in human-readable units
            let t2_us = phys.t2_ns / 1e3;
            if t2_us > 1.0 {
                ui.colored_label(
                    FOREST_GREEN,
                    egui::RichText::new(format!("T\u{2082} = {:.1} \u{00b5}s", t2_us))
                        .strong()
                        .size(14.0),
                );
            }
            dim_label(ui, "  Superconducting qubits: ~10\u{2013}100 \u{00b5}s");
        }

        ui.add_space(6.0);
        section_heading(ui, "ERROR CORRECTION");
        ui.label(format!("p = {:.4}", self.nano_p_error));
        let margin = 0.09 - self.nano_p_error;
        let mc = if margin > 0.0 { FOREST_GREEN } else { WARN_RED };
        ui.colored_label(mc, format!("Margin: {:.1}%", margin * 100.0));
        if margin > 0.0 {
            dim_label(ui, "  BELOW threshold \u{2713}");
        } else {
            ui.colored_label(WARN_RED, "  ABOVE threshold!");
        }
        ui.label(format!(
            "P_L = {:.3}  ({}/{})",
            self.nano_logical_error_rate, self.nano_logical_failures, self.nano_mc_trials_done
        ));

        // Descent results
        ui.add_space(6.0);
        section_heading(ui, "DESCENT");
        if let Some(ref cov) = self.nano_descent_cov {
            let conv_str = match cov.convergence_step {
                Some(s) => format!("step {}", s),
                None => "not converged".to_string(),
            };
            ui.colored_label(FOREST_GREEN, "Covariant (T\u{00b2}):");
            ui.label(format!("  Loss: {:.6}", cov.final_loss));
            ui.label(format!("  Conv: {}", conv_str));
            ui.label(format!("  Rate: {:.6}", cov.measured_rate));
            dim_label(ui, &format!("  Theoretical: {:.6}", cov.theoretical_rate));
        }
        if let Some(ref euc) = self.nano_descent_euc {
            let conv_str = match euc.convergence_step {
                Some(s) => format!("step {}", s),
                None => "not converged".to_string(),
            };
            ui.colored_label(WARN_RED, "Euclidean (flat):");
            ui.label(format!("  Loss: {:.6}", euc.final_loss));
            ui.label(format!("  Conv: {}", conv_str));
        }
    }

    fn draw_nano_central(&mut self, ui: &mut egui::Ui) {
        let full = ui.available_rect_before_wrap();
        let torus_h = (full.height() * 0.55).max(200.0);
        let torus_rect =
            egui::Rect::from_min_max(full.min, egui::pos2(full.max.x, full.min.y + torus_h));
        let chart_area =
            egui::Rect::from_min_max(egui::pos2(full.min.x, full.min.y + torus_h), full.max);
        let col_w = chart_area.width() / 2.0;
        let chart1 = egui::Rect::from_min_max(
            chart_area.min,
            egui::pos2(chart_area.min.x + col_w, chart_area.max.y),
        );
        let chart2 = egui::Rect::from_min_max(
            egui::pos2(chart_area.min.x + col_w, chart_area.min.y),
            chart_area.max,
        );

        // Torus interaction
        let torus_response = ui.allocate_rect(torus_rect, egui::Sense::click_and_drag());
        if torus_response.dragged() {
            let delta = torus_response.drag_delta();
            self.rotation[0] += delta.y * 0.008;
            self.rotation[1] += delta.x * 0.008;
            self.auto_rotate = false;
        }
        if torus_response.double_clicked() {
            self.auto_rotate = true;
        }

        // Draw torus with descent paths
        {
            let painter = ui.painter();
            let bundle_tag = if self.nano_params.bundle_geometry.n_resonators() > 1 {
                format!(
                    "  [{} \u{00d7}{}]",
                    self.nano_params.bundle_geometry.label(),
                    self.nano_params.bundle_geometry.n_resonators()
                )
            } else {
                String::new()
            };
            let grid_n = self.nano_params.tonnetz_grid_size;
            painter.text(
                torus_rect.center_top() + egui::vec2(0.0, 12.0),
                egui::Align2::CENTER_TOP,
                format!(
                    "{} NANOTORUS (T\u{00b2})  \u{2014}  Tonnetz {}\u{00d7}{}{}",
                    self.nano_params.material.label(),
                    grid_n,
                    grid_n,
                    bundle_tag
                ),
                egui::FontId::proportional(13.0),
                TORUS_BLUE,
            );

            let cov_steps = self.nano_descent_cov.as_ref().map(|d| d.steps.as_slice());
            let euc_steps = self.nano_descent_euc.as_ref().map(|d| d.steps.as_slice());
            draw_cnt_torus(
                painter,
                torus_rect,
                self.rotation,
                self.nano_params.tonnetz_grid_size,
                self.nano_snapshot.as_ref(),
                self.time,
            );

            // Overlay descent paths
            let rm = 1.2_f32;
            let rn = 0.45_f32;
            if let Some(steps) = cov_steps {
                draw_descent_path(
                    painter,
                    torus_rect,
                    self.rotation,
                    rm,
                    rn,
                    steps,
                    true,
                    self.time,
                );
            }
            if self.nano_show_euclidean {
                if let Some(steps) = euc_steps {
                    draw_descent_path(
                        painter,
                        torus_rect,
                        self.rotation,
                        rm,
                        rn,
                        steps,
                        false,
                        self.time,
                    );
                }
            }

            // Chart titles
            painter.text(
                chart1.center_top() + egui::vec2(0.0, 4.0),
                egui::Align2::CENTER_TOP,
                "THRESHOLD CURVE",
                egui::FontId::proportional(11.0),
                HEADING_CLR,
            );
            painter.text(
                chart2.center_top() + egui::vec2(0.0, 4.0),
                egui::Align2::CENTER_TOP,
                "DESCENT CONVERGENCE",
                egui::FontId::proportional(11.0),
                HEADING_CLR,
            );
        }

        // Chart 1: Threshold sweep
        let chart1_inner = egui::Rect::from_min_max(
            chart1.min + egui::vec2(10.0, 22.0),
            chart1.max - egui::vec2(10.0, 5.0),
        );
        let p_error = self.nano_p_error;
        let logical_error_rate = self.nano_logical_error_rate;

        ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart1_inner), |ui| {
            let plot = Plot::new("nano_threshold_chart")
                .width(chart1_inner.width())
                .height(chart1_inner.height())
                .x_axis_label("p")
                .y_axis_label("P_L")
                .include_x(0.0)
                .include_x(0.2)
                .include_y(0.0)
                .include_y(1.0)
                .show_axes(true)
                .allow_zoom(true)
                .allow_drag(true)
                .legend(Legend::default().position(Corner::LeftTop));

            plot.show(ui, |plot_ui| {
                let zone_pts: PlotPoints = vec![[0.0, 0.0], [0.09, 0.0], [0.09, 1.0], [0.0, 1.0]]
                    .into_iter()
                    .collect();
                plot_ui.polygon(
                    Polygon::new(zone_pts)
                        .fill_color(egui::Color32::from_rgba_unmultiplied(86, 166, 96, 20))
                        .stroke(egui::Stroke::NONE)
                        .name("Correctable zone"),
                );

                let colors = [
                    FOREST_GREEN,
                    GOLD_EG,
                    egui::Color32::from_rgb(200, 200, 190),
                    X_ERROR_RED,
                ];
                let markers = [
                    MarkerShape::Circle,
                    MarkerShape::Diamond,
                    MarkerShape::Square,
                    MarkerShape::Up,
                ];

                if let Some(ref cd) = self.nano_chart_data {
                    for (i, curve) in cd.curves.iter().enumerate() {
                        let pts: PlotPoints = curve.points.iter().map(|&(p, pl)| [p, pl]).collect();
                        let scatter_pts: PlotPoints =
                            curve.points.iter().map(|&(p, pl)| [p, pl]).collect();
                        let color = colors[i % colors.len()];
                        let marker = markers[i % markers.len()];
                        let name = format!("N={}", curve.n);
                        plot_ui.line(Line::new(pts).color(color).width(2.0).name(&name));
                        plot_ui.points(
                            Points::new(scatter_pts)
                                .color(color)
                                .shape(marker)
                                .radius(3.5)
                                .name(&name),
                        );
                    }
                }

                if p_error > 0.0 {
                    plot_ui.vline(
                        VLine::new(p_error)
                            .color(egui::Color32::WHITE)
                            .width(1.5)
                            .name("Operating point"),
                    );
                    plot_ui.text(
                        PlotText::new(
                            PlotPoint::new(p_error, logical_error_rate.max(0.05)),
                            egui::RichText::new(format!("p={:.4}", p_error))
                                .size(10.0)
                                .color(egui::Color32::WHITE),
                        )
                        .anchor(egui::Align2::LEFT_BOTTOM),
                    );
                }
                plot_ui.vline(
                    VLine::new(0.09)
                        .color(egui::Color32::from_rgba_unmultiplied(230, 70, 70, 120))
                        .width(1.0)
                        .name("Threshold ~9%"),
                );
            });
        });

        // Chart 2: Descent convergence (loss vs iteration)
        let chart2_inner = egui::Rect::from_min_max(
            chart2.min + egui::vec2(10.0, 22.0),
            chart2.max - egui::vec2(10.0, 5.0),
        );
        ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart2_inner), |ui| {
            let plot = Plot::new("nano_descent_chart")
                .width(chart2_inner.width())
                .height(chart2_inner.height())
                .x_axis_label("iteration")
                .y_axis_label("loss")
                .show_axes(true)
                .allow_zoom(true)
                .allow_drag(true)
                .legend(Legend::default().position(Corner::RightTop));

            plot.show(ui, |plot_ui| {
                if let Some(ref cov) = self.nano_descent_cov {
                    let pts: PlotPoints = cov
                        .steps
                        .iter()
                        .map(|s| [s.iteration as f64, s.loss])
                        .collect();
                    plot_ui.line(
                        Line::new(pts)
                            .color(FOREST_GREEN)
                            .width(2.0)
                            .name("Covariant (T\u{00b2})"),
                    );
                }
                if self.nano_show_euclidean {
                    if let Some(ref euc) = self.nano_descent_euc {
                        let pts: PlotPoints = euc
                            .steps
                            .iter()
                            .map(|s| [s.iteration as f64, s.loss])
                            .collect();
                        plot_ui.line(
                            Line::new(pts)
                                .color(WARN_RED)
                                .width(1.5)
                                .name("Euclidean (flat)"),
                        );
                    }
                }
            });
        });
    }

    fn draw_nano_status(&self, ctx: &egui::Context) {
        if let Some(ref phys) = self.nano_physics_result {
            let (st, sc) = if self.nano_p_error < 0.09 {
                ("CORRECTABLE", FOREST_GREEN)
            } else {
                ("TOO NOISY", WARN_RED)
            };
            let (coh_st, coh_sc) = if phys.t2_ns < 1.0 {
                ("NEGLIGIBLE", WARN_RED)
            } else if phys.tonnetz_enhancement > 5.0 && phys.t2_ns > self.nano_gate_time_ns {
                ("EFFECTIVE", FOREST_GREEN)
            } else if phys.tonnetz_enhancement > 1.5 {
                ("MODERATE", GOLD_EG)
            } else {
                ("MARGINAL", WARN_RED)
            };
            let frame = egui::Frame {
                fill: egui::Color32::from_rgba_unmultiplied(22, 28, 22, 230),
                corner_radius: egui::CornerRadius::from(6),
                inner_margin: egui::Margin::same(10),
                stroke: egui::Stroke::new(2.0, sc),
                ..Default::default()
            };
            egui::Window::new("nano_status")
                .title_bar(false)
                .resizable(false)
                .movable(false)
                .frame(frame)
                .anchor(egui::Align2::RIGHT_BOTTOM, [-10.0, -10.0])
                .show(ctx, |ui| {
                    ui.horizontal(|ui| {
                        ui.colored_label(sc, egui::RichText::new(st).strong().size(15.0));
                        ui.separator();
                        ui.colored_label(
                            coh_sc,
                            egui::RichText::new(format!("Coherence {}", coh_st))
                                .strong()
                                .size(13.0),
                        );
                    });
                    ui.label(format!(
                        "T\u{2082}={:.0}ns  p={:.4}  P_L={:.3}",
                        phys.t2_ns, self.nano_p_error, self.nano_logical_error_rate
                    ));
                    dim_label(
                        ui,
                        &format!(
                            "NANOTORUS: Q={:.0} +{:.0}ns ({:.0}\u{00d7})",
                            phys.q_mech,
                            phys.t2_ns - phys.t2_bare_ns,
                            phys.tonnetz_enhancement
                        ),
                    );
                    let n_q = (self.nano_params.tonnetz_grid_size
                        * self.nano_params.tonnetz_grid_size)
                        as usize;
                    let gap_t =
                        crate::coherence::spectral_gap(crate::coherence::Topology::Toroidal, n_q);
                    let gap_l =
                        crate::coherence::spectral_gap(crate::coherence::Topology::Linear, n_q);
                    dim_label(
                        ui,
                        &format!(
                            "T\u{00b2} vs chain: {:.1}\u{00d7} spectral advantage",
                            gap_t / gap_l
                        ),
                    );
                    if let Some(ref cov) = self.nano_descent_cov {
                        let target_name = match self.nano_descent_target {
                            NanoDescentTarget::RingGeometry => "Ring",
                            NanoDescentTarget::TonnetzFilter => "Tonnetz",
                            NanoDescentTarget::Cooling => "Cooling",
                        };
                        let conv = if cov.converged {
                            "converged"
                        } else {
                            "running"
                        };
                        dim_label(
                            ui,
                            &format!(
                                "Descent ({}): {} rate={:.4}",
                                target_name, conv, cov.measured_rate
                            ),
                        );
                    }
                    if self.paused {
                        ui.colored_label(GOLD_EG, egui::RichText::new("PAUSED").size(11.0));
                    }
                });
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Logo Decoded tab: Spinning sphere inside torus → orthogonal force
// ═══════════════════════════════════════════════════════════════════════════════

const LOGO_PURPLE: egui::Color32 = egui::Color32::from_rgb(167, 139, 250);
const LOGO_CYAN: egui::Color32 = egui::Color32::from_rgb(34, 211, 238);
const LOGO_RED: egui::Color32 = egui::Color32::from_rgb(248, 113, 113);
const LOGO_AMBER: egui::Color32 = egui::Color32::from_rgb(251, 191, 36);

impl QuantumEngineApp {
    // ─── Controls (left sidebar) ────────────────────────────────────────────

    fn draw_logo_controls(&mut self, ui: &mut egui::Ui) {
        ui.colored_label(
            LOGO_PURPLE,
            egui::RichText::new("THE LOGO DECODED").strong().size(13.0),
        );
        dim_label(ui, "Prior art \u{2014} November 2023");
        ui.add_space(4.0);

        section_heading(ui, "TOROIDAL ENGINE");
        ui.add_space(2.0);

        ui.label("Sphere rotation speed");
        ui.add(egui::Slider::new(&mut self.logo_sphere_speed, 0.0..=5.0).text("rad/s"));
        ui.add_space(4.0);

        ui.label("Torus major radius R");
        ui.add(egui::Slider::new(&mut self.logo_torus_major, 0.6..=2.0).text("R"));
        ui.label("Torus minor radius r");
        ui.add(egui::Slider::new(&mut self.logo_torus_minor, 0.15..=0.8).text("r"));
        ui.add_space(4.0);

        section_heading(ui, "TONNETZ LATTICE");
        let mut n_f = self.logo_lattice_n as f64;
        ui.add(
            egui::Slider::new(&mut n_f, 4.0..=24.0)
                .integer()
                .text("N\u{00d7}N"),
        );
        self.logo_lattice_n = n_f as usize;
        ui.add_space(4.0);

        section_heading(ui, "OVERLAYS");
        ui.checkbox(&mut self.logo_show_force, "Orthogonal force vectors");
        ui.checkbox(&mut self.logo_show_tonnetz, "Tonnetz lattice nodes");
        ui.checkbox(&mut self.logo_show_bloch_axes, "Bloch sphere axes");
        ui.checkbox(&mut self.logo_show_triadic, "Triadic coherence cell");
        ui.add_space(8.0);

        section_heading(ui, "LOGO ELEMENTS");
        ui.add_space(2.0);
        let items = [
            (
                "\u{25cb} Large circle",
                "Torus T\u{00b2} \u{2014} constraint manifold",
                LOGO_PURPLE,
            ),
            (
                "\u{25cf} Filled node",
                "Karmonic functional H eval point",
                FOREST_GREEN,
            ),
            (
                "\u{25cb}\u{25cb}\u{25cb} Open nodes",
                "Triadic coherence cell",
                LOGO_CYAN,
            ),
            ("\u{2500} Edges", "Graph Laplacian structure E", LOGO_AMBER),
        ];
        for (elem, desc, color) in items {
            ui.horizontal(|ui| {
                ui.colored_label(color, egui::RichText::new(elem).strong().size(12.0));
            });
            dim_label(ui, desc);
            ui.add_space(2.0);
        }

        ui.add_space(8.0);
        section_heading(ui, "THE INSIGHT");
        dim_label(ui, "A spinning sphere inside a toroid");
        dim_label(ui, "generates orthogonal force from");
        dim_label(
            ui,
            "\u{03c0}\u{2081}(T\u{00b2}) = \u{2124}\u{00d7}\u{2124} topology.",
        );
        ui.add_space(4.0);
        dim_label(ui, "Same geometry controls:");
        let domains = [
            ("Quantum coherence time", LOGO_CYAN),
            ("LLM hallucination reduction", LOGO_PURPLE),
            ("Propulsive thrust", LOGO_RED),
        ];
        for (d, c) in domains {
            ui.colored_label(c, egui::RichText::new(d).size(12.0));
        }
    }

    // ─── Results (right sidebar) ────────────────────────────────────────────

    fn draw_logo_results(&mut self, ui: &mut egui::Ui) {
        let n = self.logo_lattice_n;
        let torus = crate::torus::TorusLattice::new(n, 1.0);
        let gap = torus.spectral_gap();
        let n_q = n * n;
        let gap_linear = crate::coherence::spectral_gap(crate::coherence::Topology::Linear, n_q);
        let gap_complete =
            crate::coherence::spectral_gap(crate::coherence::Topology::Complete, n_q);
        let mixing = torus.mixing_time_lattice();
        let poincare = 1.0 / gap;
        let coherence_norm =
            crate::coherence::coherence_time_normalized(gap, 1.0_f64 / std::f64::consts::E);

        section_heading(ui, "SPECTRAL GAP");
        ui.colored_label(
            LOGO_PURPLE,
            egui::RichText::new(format!("\u{03bb}\u{2081} = {:.6}", gap))
                .strong()
                .size(16.0),
        );
        dim_label(ui, &format!("N={} \u{2192} {}x{} torus", n, n, n));
        dim_label(ui, &format!("{} qubits on T\u{00b2}", n_q));
        ui.add_space(4.0);

        ui.colored_label(
            LABEL_CLR,
            egui::RichText::new("Topology comparison")
                .strong()
                .size(12.0),
        );
        ui.horizontal(|ui| {
            ui.colored_label(LOGO_PURPLE, "T\u{00b2}:");
            ui.label(format!("{:.4}", gap));
        });
        ui.horizontal(|ui| {
            ui.colored_label(WARN_RED, "Linear:");
            ui.label(format!("{:.4}", gap_linear));
        });
        ui.horizontal(|ui| {
            ui.colored_label(FOREST_GREEN, "Complete:");
            ui.label(format!("{:.1}", gap_complete));
        });
        dim_label(
            ui,
            &format!(
                "T\u{00b2}/Linear advantage: {:.1}\u{00d7}",
                gap / gap_linear
            ),
        );
        ui.add_space(8.0);

        section_heading(ui, "DERIVED QUANTITIES");
        ui.horizontal(|ui| {
            ui.colored_label(LOGO_CYAN, "Mixing time:");
            ui.label(format!("{:.2}", mixing));
        });
        ui.horizontal(|ui| {
            ui.colored_label(LOGO_CYAN, "Poincar\u{00e9} const:");
            ui.label(format!("{:.2}", poincare));
        });
        ui.horizontal(|ui| {
            ui.colored_label(LOGO_CYAN, "Coherence \u{03c4}/\u{03b3}:");
            ui.label(format!("{:.2}", coherence_norm));
        });
        ui.add_space(8.0);

        // Orthogonal thrust metric (dimensionless, proportional to λ₁ × ω²)
        let omega = self.logo_sphere_speed;
        let thrust_metric = gap * omega * omega;
        section_heading(ui, "ORTHOGONAL FORCE");
        ui.colored_label(
            LOGO_RED,
            egui::RichText::new(format!("F\u{22a5} \u{221d} {:.4}", thrust_metric))
                .strong()
                .size(16.0),
        );
        dim_label(
            ui,
            &format!(
                "\u{03bb}\u{2081}\u{00d7}\u{03c9}\u{00b2} = {:.6}\u{00d7}{:.2}\u{00b2}",
                gap, omega
            ),
        );
        ui.add_space(4.0);
        dim_label(ui, "Force emerges from topology:");
        dim_label(ui, "\u{03c0}\u{2081}(T\u{00b2}) = \u{2124}\u{00d7}\u{2124}");
        dim_label(ui, "Two winding numbers \u{2192}");
        dim_label(ui, "confined toroidal + free poloidal");
        dim_label(ui, "\u{2192} axial orthogonal force");
        ui.add_space(8.0);

        section_heading(ui, "STRUCTURAL PARALLEL");
        let rows = [
            ("Topology", "S\u{00b2} compact", "T\u{00b2} compact"),
            (
                "Coords",
                "(\u{03b8},\u{03c6})",
                "(\u{03b8}\u{2081},\u{03b8}\u{2082})",
            ),
            ("Spectrum", "Hamiltonian", "Laplacian \u{03bb}\u{2081}"),
            ("Coherence", "Unitarity", "Spectral gap"),
            ("Protect", "Toric code", "Logit bias +2.8pp"),
        ];
        egui::Grid::new("structural_parallel")
            .striped(true)
            .show(ui, |ui| {
                ui.colored_label(LOGO_AMBER, egui::RichText::new("").strong().size(11.0));
                ui.colored_label(
                    LOGO_CYAN,
                    egui::RichText::new("Bloch S\u{00b2}").strong().size(11.0),
                );
                ui.colored_label(
                    LOGO_PURPLE,
                    egui::RichText::new("Tonnetz T\u{00b2}").strong().size(11.0),
                );
                ui.end_row();
                for (prop, bloch, tonnetz) in rows {
                    ui.colored_label(LOGO_AMBER, egui::RichText::new(prop).size(11.0));
                    ui.label(egui::RichText::new(bloch).size(11.0));
                    ui.label(egui::RichText::new(tonnetz).size(11.0));
                    ui.end_row();
                }
            });
        ui.add_space(8.0);

        section_heading(ui, "PRIOR ART TIMELINE");
        let events = [
            ("Nov 2023", "Logo created", true),
            ("2023-24", "Paraxiom Inc. est.", true),
            ("Feb 7 2026", "TLB paper (Zenodo)", false),
            ("Feb 10 2026", "Defensive disclosure", false),
            ("Feb 15 2026", "Logo decoded", true),
        ];
        for (date, event, highlight) in events {
            ui.horizontal(|ui| {
                let c = if highlight { LOGO_PURPLE } else { DIM };
                ui.colored_label(c, egui::RichText::new(date).strong().size(10.0));
                ui.label(egui::RichText::new(event).size(10.0));
            });
        }
    }

    // ─── Central panel: 3D torus with spinning sphere ───────────────────────

    fn draw_logo_central(&mut self, ui: &mut egui::Ui) {
        if !self.paused {
            let dt = ui.input(|i| i.predicted_dt);
            self.logo_sphere_angle += dt * self.logo_sphere_speed as f32;
        }

        let rect = ui.available_rect_before_wrap();
        let painter = ui.painter_at(rect);

        // Background
        painter.rect_filled(rect, 0.0, egui::Color32::from_rgb(10, 14, 10));

        let rm = self.logo_torus_major;
        let rn = self.logo_torus_minor;
        let rot = self.rotation;
        let time = self.time;
        let rings = 24_usize;
        let segs = 48_usize;

        // ── Torus surface patches (semi-transparent purple) ─────────────
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
                let alpha = (14.0 + 18.0 * depth_t) as u8;
                let r = (40.0 + 40.0 * depth_t) as u8;
                let g = (20.0 + 30.0 * depth_t) as u8;
                let b = (80.0 + 60.0 * depth_t) as u8;

                let mesh = egui::Mesh {
                    indices: vec![0, 1, 2, 0, 2, 3],
                    vertices: vec![
                        egui::epaint::Vertex {
                            pos: p00,
                            uv: egui::epaint::WHITE_UV,
                            color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                        },
                        egui::epaint::Vertex {
                            pos: p10,
                            uv: egui::epaint::WHITE_UV,
                            color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                        },
                        egui::epaint::Vertex {
                            pos: p11,
                            uv: egui::epaint::WHITE_UV,
                            color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                        },
                        egui::epaint::Vertex {
                            pos: p01,
                            uv: egui::epaint::WHITE_UV,
                            color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                        },
                    ],
                    texture_id: egui::TextureId::default(),
                };
                painter.add(egui::Shape::mesh(mesh));
            }
        }

        // ── Torus wireframe ─────────────────────────────────────────────
        for ring in 0..rings {
            let fixed = 2.0 * PI * ring as f32 / rings as f32;
            for s in 0..segs {
                let a = 2.0 * PI * s as f32 / segs as f32;
                let b = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;
                // u-rings
                let (s1, z1) = project(torus_pt(rm, rn, fixed, a), rot, rect);
                let (s2, _z2) = project(torus_pt(rm, rn, fixed, b), rot, rect);
                let al = depth_alpha(z1);
                painter.line_segment(
                    [s1, s2],
                    egui::Stroke::new(0.5, egui::Color32::from_rgba_unmultiplied(80, 60, 140, al)),
                );
                // v-rings
                let (s1, z1) = project(torus_pt(rm, rn, a, fixed), rot, rect);
                let (s2, _z2) = project(torus_pt(rm, rn, b, fixed), rot, rect);
                let al = depth_alpha(z1);
                painter.line_segment(
                    [s1, s2],
                    egui::Stroke::new(0.5, egui::Color32::from_rgba_unmultiplied(80, 60, 140, al)),
                );
            }
        }

        // ── Non-contractible cycles (gold pulsing) ──────────────────────
        for &(cycle_u, fixed_other) in &[(true, 0.0_f32), (true, PI), (false, 0.0), (false, PI)] {
            for s in 0..segs {
                let a = 2.0 * PI * s as f32 / segs as f32;
                let b = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;
                let (p1, p2) = if cycle_u {
                    (
                        torus_pt(rm, rn, fixed_other, a),
                        torus_pt(rm, rn, fixed_other, b),
                    )
                } else {
                    (
                        torus_pt(rm, rn, a, fixed_other),
                        torus_pt(rm, rn, b, fixed_other),
                    )
                };
                let (sc1, _) = project(p1, rot, rect);
                let (sc2, _) = project(p2, rot, rect);
                let pulse = 0.55 + 0.45 * (a + time * if cycle_u { -2.0 } else { 1.5 }).sin();
                let r = (212.0 * pulse + 80.0 * (1.0 - pulse)) as u8;
                let g = (175.0 * pulse + 100.0 * (1.0 - pulse)) as u8;
                let bl = (55.0 * pulse + 30.0 * (1.0 - pulse)) as u8;
                painter.line_segment(
                    [sc1, sc2],
                    egui::Stroke::new(2.0, egui::Color32::from_rgb(r, g, bl)),
                );
            }
        }

        // ── Tonnetz lattice nodes on torus surface ──────────────────────
        if self.logo_show_tonnetz {
            let grid = self.logo_lattice_n;
            for row in 0..grid {
                for col in 0..grid {
                    let u = 2.0 * PI * row as f32 / grid as f32;
                    let v = 2.0 * PI * col as f32 / grid as f32;
                    let (sp, z) = project(torus_pt(rm, rn + 0.015, u, v), rot, rect);
                    let al = depth_alpha(z);
                    let phase_v = 0.6 + 0.4 * (time * 2.0 + u + v).sin();
                    let br = (180.0 * phase_v) as u8;
                    painter.circle_filled(
                        sp,
                        2.0,
                        egui::Color32::from_rgba_unmultiplied(br, br, (br as f32 * 0.8) as u8, al),
                    );
                }
            }
        }

        // ── Spinning Bloch sphere at torus center ───────────────────────
        // The sphere sits in the "hole" of the torus (at the origin).
        let sphere_r = rn * 0.65;
        let sphere_segs = 32_usize;
        let angle = self.logo_sphere_angle;

        // Sphere wireframe (equator + meridians)
        for m in 0..3 {
            let meridian_offset = PI * m as f32 / 3.0;
            for s in 0..sphere_segs {
                let t0 = 2.0 * PI * s as f32 / sphere_segs as f32;
                let t1 = 2.0 * PI * ((s + 1) % sphere_segs) as f32 / sphere_segs as f32;

                // Equator (rotates with sphere)
                if m == 0 {
                    let eq0 = [
                        sphere_r * (t0 + angle).cos(),
                        sphere_r * (t0 + angle).sin(),
                        0.0,
                    ];
                    let eq1 = [
                        sphere_r * (t1 + angle).cos(),
                        sphere_r * (t1 + angle).sin(),
                        0.0,
                    ];
                    let (a, za) = project(eq0, rot, rect);
                    let (b, _) = project(eq1, rot, rect);
                    let al = depth_alpha(za);
                    painter.line_segment(
                        [a, b],
                        egui::Stroke::new(
                            1.5,
                            egui::Color32::from_rgba_unmultiplied(34, 211, 238, al),
                        ),
                    );
                }

                // Meridians
                let mer0 = [
                    sphere_r * t0.sin() * (meridian_offset + angle).cos(),
                    sphere_r * t0.sin() * (meridian_offset + angle).sin(),
                    sphere_r * t0.cos(),
                ];
                let mer1 = [
                    sphere_r * t1.sin() * (meridian_offset + angle).cos(),
                    sphere_r * t1.sin() * (meridian_offset + angle).sin(),
                    sphere_r * t1.cos(),
                ];
                let (a, za) = project(mer0, rot, rect);
                let (b, _) = project(mer1, rot, rect);
                let al = depth_alpha(za);
                painter.line_segment(
                    [a, b],
                    egui::Stroke::new(
                        1.0,
                        egui::Color32::from_rgba_unmultiplied(
                            34,
                            211,
                            238,
                            (al as f32 * 0.7) as u8,
                        ),
                    ),
                );
            }
        }

        // Bloch vector (state vector spinning inside sphere)
        let state_theta = PI * 0.35;
        let state_phi = angle * 2.3;
        let state_pos = [
            sphere_r * state_theta.sin() * state_phi.cos(),
            sphere_r * state_theta.sin() * state_phi.sin(),
            sphere_r * state_theta.cos(),
        ];
        let (origin_s, _) = project([0.0, 0.0, 0.0], rot, rect);
        let (state_s, _) = project(state_pos, rot, rect);
        painter.line_segment([origin_s, state_s], egui::Stroke::new(2.5, LOGO_CYAN));
        painter.circle_filled(state_s, 5.0, LOGO_CYAN);

        // Bloch sphere axes
        if self.logo_show_bloch_axes {
            let axes: [([f32; 3], &str, egui::Color32); 4] = [
                ([sphere_r * 1.15, 0.0, 0.0], "|+x>", LOGO_CYAN),
                ([0.0, sphere_r * 1.15, 0.0], "|+y>", LOGO_PURPLE),
                ([0.0, 0.0, sphere_r * 1.15], "|0>", FOREST_GREEN),
                ([0.0, 0.0, -sphere_r * 1.15], "|1>", WARN_RED),
            ];
            for (pos, label, color) in axes {
                let (p, _) = project(pos, rot, rect);
                painter.circle_filled(p, 3.0, color);
                painter.text(
                    egui::pos2(p.x + 6.0, p.y - 6.0),
                    egui::Align2::LEFT_BOTTOM,
                    label,
                    egui::FontId::monospace(10.0),
                    color,
                );
            }
        }

        // ── Triadic coherence cell ──────────────────────────────────────
        if self.logo_show_triadic {
            let triad_y = rn + 0.5;
            let node_positions: [[f32; 3]; 3] = [
                [-0.5, 0.0, -triad_y],
                [0.5, 0.0, -triad_y],
                [0.0, 0.0, -triad_y - 0.4],
            ];
            let center_pos = [0.0_f32, 0.0, -triad_y + 0.15];

            for node in &node_positions {
                let (np, _) = project(*node, rot, rect);
                let (cp, _) = project(center_pos, rot, rect);
                painter.line_segment(
                    [np, cp],
                    egui::Stroke::new(2.0, egui::Color32::from_rgb(100, 100, 90)),
                );
            }

            let (cp, _) = project(center_pos, rot, rect);
            painter.circle_filled(cp, 7.0, egui::Color32::WHITE);
            painter.text(
                egui::pos2(cp.x + 10.0, cp.y),
                egui::Align2::LEFT_CENTER,
                "H(q)",
                egui::FontId::monospace(11.0),
                LOGO_AMBER,
            );

            let triad_labels = ["c12", "c13", "c23"];
            for (i, node) in node_positions.iter().enumerate() {
                let (np, _) = project(*node, rot, rect);
                painter.circle_stroke(np, 6.0, egui::Stroke::new(2.0, LOGO_CYAN));
                painter.text(
                    egui::pos2(np.x + 8.0, np.y + 2.0),
                    egui::Align2::LEFT_CENTER,
                    triad_labels[i],
                    egui::FontId::monospace(10.0),
                    LOGO_CYAN,
                );
            }
        }

        // ── Orthogonal force arrows (along torus axis = z-axis) ─────────
        if self.logo_show_force {
            let arrow_base = rn + 0.08;
            let arrow_tip = rn + 0.6;
            let pulse = 0.4 + 0.6 * (time * 3.0).sin().abs();
            let alpha = (180.0 * pulse) as u8;
            let force_color = egui::Color32::from_rgba_unmultiplied(248, 113, 113, alpha);

            // Up arrow
            let (base_up, _) = project([0.0, 0.0, arrow_base], rot, rect);
            let (tip_up, _) = project([0.0, 0.0, arrow_tip], rot, rect);
            painter.line_segment([base_up, tip_up], egui::Stroke::new(3.5, force_color));
            // Arrowhead
            let dx = tip_up.x - base_up.x;
            let dy = tip_up.y - base_up.y;
            let len = (dx * dx + dy * dy).sqrt().max(1.0);
            let ux = dx / len;
            let uy = dy / len;
            let head_size = 10.0;
            let h1 = egui::pos2(
                tip_up.x - ux * head_size + uy * head_size * 0.5,
                tip_up.y - uy * head_size - ux * head_size * 0.5,
            );
            let h2 = egui::pos2(
                tip_up.x - ux * head_size - uy * head_size * 0.5,
                tip_up.y - uy * head_size + ux * head_size * 0.5,
            );
            painter.add(egui::Shape::convex_polygon(
                vec![tip_up, h1, h2],
                force_color,
                egui::Stroke::NONE,
            ));

            // Down arrow
            let (base_dn, _) = project([0.0, 0.0, -arrow_base], rot, rect);
            let (tip_dn, _) = project([0.0, 0.0, -arrow_tip], rot, rect);
            painter.line_segment([base_dn, tip_dn], egui::Stroke::new(3.5, force_color));
            let dx = tip_dn.x - base_dn.x;
            let dy = tip_dn.y - base_dn.y;
            let len = (dx * dx + dy * dy).sqrt().max(1.0);
            let ux = dx / len;
            let uy = dy / len;
            let h1 = egui::pos2(
                tip_dn.x - ux * head_size + uy * head_size * 0.5,
                tip_dn.y - uy * head_size - ux * head_size * 0.5,
            );
            let h2 = egui::pos2(
                tip_dn.x - ux * head_size - uy * head_size * 0.5,
                tip_dn.y - uy * head_size + ux * head_size * 0.5,
            );
            painter.add(egui::Shape::convex_polygon(
                vec![tip_dn, h1, h2],
                force_color,
                egui::Stroke::NONE,
            ));

            // Labels
            painter.text(
                egui::pos2(tip_up.x + 12.0, tip_up.y),
                egui::Align2::LEFT_CENTER,
                "F\u{22a5} THRUST",
                egui::FontId::monospace(12.0),
                LOGO_RED,
            );
            painter.text(
                egui::pos2(tip_dn.x + 12.0, tip_dn.y),
                egui::Align2::LEFT_CENTER,
                "F\u{22a5} THRUST",
                egui::FontId::monospace(12.0),
                LOGO_RED,
            );

            // Toroidal circulation arrows
            let circ_segs = 36_usize;
            for s in 0..circ_segs {
                let t0 = 2.0 * PI * s as f32 / circ_segs as f32;
                let t1 = 2.0 * PI * ((s + 1) % circ_segs) as f32 / circ_segs as f32;
                let r_circ = rm + rn * 0.3;
                let c0 = [r_circ * t0.cos(), r_circ * t0.sin(), 0.0_f32];
                let c1 = [r_circ * t1.cos(), r_circ * t1.sin(), 0.0];
                let (a, za) = project(c0, rot, rect);
                let (b, _) = project(c1, rot, rect);
                let al = depth_alpha(za);
                let dash_pulse = 0.4 + 0.6 * ((t0 * 3.0 - time * 2.0).sin() * 0.5 + 0.5);
                let lp = (LOGO_PURPLE.r() as f32 * dash_pulse) as u8;
                let gp = (LOGO_PURPLE.g() as f32 * dash_pulse) as u8;
                let bp = (LOGO_PURPLE.b() as f32 * dash_pulse) as u8;
                painter.line_segment(
                    [a, b],
                    egui::Stroke::new(
                        1.5,
                        egui::Color32::from_rgba_unmultiplied(lp, gp, bp, (al as f32 * 0.6) as u8),
                    ),
                );
            }
        }

        // ── Title and theory labels ─────────────────────────────────────
        painter.text(
            egui::pos2(rect.left() + 20.0, rect.top() + 20.0),
            egui::Align2::LEFT_TOP,
            "SPINNING SPHERE INSIDE TORUS \u{2192} ORTHOGONAL FORCE",
            egui::FontId::monospace(14.0),
            LOGO_PURPLE,
        );
        painter.text(
            egui::pos2(rect.left() + 20.0, rect.top() + 38.0),
            egui::Align2::LEFT_TOP,
            "Bloch S\u{00b2} inside Tonnetz T\u{00b2} \u{2014} Prior Art Nov 2023",
            egui::FontId::monospace(11.0),
            DIM,
        );

        // Physics pipeline at bottom
        let pipeline_y = rect.bottom() - 35.0;
        let labels = [
            "CNT Resonator",
            "\u{2192}",
            "Doppler Cooling",
            "\u{2192}",
            "Tonnetz Filter",
            "\u{2192}",
            "Toric Code",
        ];
        let colors = [
            LOGO_CYAN,
            DIM,
            TORUS_BLUE,
            DIM,
            LOGO_PURPLE,
            DIM,
            FOREST_GREEN,
        ];
        let mut px = rect.left() + 20.0;
        for (label, color) in labels.iter().zip(colors.iter()) {
            painter.text(
                egui::pos2(px, pipeline_y),
                egui::Align2::LEFT_TOP,
                label,
                egui::FontId::monospace(11.0),
                *color,
            );
            px += label.len() as f32 * 7.5 + 8.0;
        }

        // Spectral gap chart (bottom right area)
        let chart_rect = egui::Rect::from_min_size(
            egui::pos2(rect.right() - 280.0, rect.bottom() - 180.0),
            egui::vec2(260.0, 160.0),
        );
        if rect.width() > 600.0 && rect.height() > 400.0 {
            painter.rect_filled(
                chart_rect,
                6.0,
                egui::Color32::from_rgba_unmultiplied(15, 20, 15, 200),
            );
            painter.rect_stroke(
                chart_rect,
                6.0,
                egui::Stroke::new(1.0, egui::Color32::from_rgb(40, 50, 40)),
                egui::epaint::StrokeKind::Outside,
            );
            painter.text(
                egui::pos2(chart_rect.left() + 8.0, chart_rect.top() + 6.0),
                egui::Align2::LEFT_TOP,
                "\u{03bb}\u{2081}(N) Spectral Gap vs Lattice Size",
                egui::FontId::monospace(10.0),
                LOGO_AMBER,
            );

            let sizes = [4_usize, 6, 8, 10, 12, 16, 20, 24];
            let max_gap = 2.0_f32;
            let chart_inner = egui::Rect::from_min_max(
                egui::pos2(chart_rect.left() + 30.0, chart_rect.top() + 22.0),
                egui::pos2(chart_rect.right() - 10.0, chart_rect.bottom() - 20.0),
            );

            for (i, &n) in sizes.iter().enumerate() {
                let gap = 2.0 - 2.0 * (2.0 * std::f64::consts::PI / n as f64).cos();
                let x = chart_inner.left()
                    + (i as f32 / (sizes.len() - 1) as f32) * chart_inner.width();
                let y = chart_inner.bottom() - (gap as f32 / max_gap) * chart_inner.height();

                let is_current = n == self.logo_lattice_n;
                let dot_r = if is_current { 5.0 } else { 3.0 };
                let c = if is_current { LOGO_PURPLE } else { LOGO_CYAN };
                painter.circle_filled(egui::pos2(x, y), dot_r, c);

                if i > 0 {
                    let prev_gap =
                        2.0 - 2.0 * (2.0 * std::f64::consts::PI / sizes[i - 1] as f64).cos();
                    let ppx = chart_inner.left()
                        + ((i - 1) as f32 / (sizes.len() - 1) as f32) * chart_inner.width();
                    let py =
                        chart_inner.bottom() - (prev_gap as f32 / max_gap) * chart_inner.height();
                    painter.line_segment(
                        [egui::pos2(ppx, py), egui::pos2(x, y)],
                        egui::Stroke::new(1.5, LOGO_CYAN),
                    );
                }

                painter.text(
                    egui::pos2(x, chart_inner.bottom() + 4.0),
                    egui::Align2::CENTER_TOP,
                    &format!("{}", n),
                    egui::FontId::monospace(9.0),
                    DIM,
                );
            }
        }

        // Mouse drag for rotation
        let resp = ui.interact(rect, egui::Id::new("logo_torus_drag"), egui::Sense::drag());
        if resp.dragged() {
            self.rotation[0] += resp.drag_delta().y * 0.01;
            self.rotation[1] += resp.drag_delta().x * 0.01;
        } else if self.auto_rotate && !self.paused {
            self.rotation[1] += 0.004;
        }
    }

    // ─── Status badge ───────────────────────────────────────────────────

    fn draw_logo_status(&self, ctx: &egui::Context) {
        let n = self.logo_lattice_n;
        let gap = crate::torus::TorusLattice::new(n, 1.0).spectral_gap();
        let omega = self.logo_sphere_speed;
        let thrust = gap * omega * omega;

        let sc = if thrust > 0.5 {
            FOREST_GREEN
        } else if thrust > 0.1 {
            GOLD_EG
        } else {
            WARN_RED
        };
        let st = if thrust > 0.5 {
            "STRONG"
        } else if thrust > 0.1 {
            "MODERATE"
        } else {
            "WEAK"
        };

        let frame = egui::Frame {
            fill: egui::Color32::from_rgba_unmultiplied(22, 18, 32, 230),
            corner_radius: egui::CornerRadius::from(6),
            inner_margin: egui::Margin::same(10),
            stroke: egui::Stroke::new(2.0, LOGO_PURPLE),
            ..Default::default()
        };
        egui::Window::new("logo_status")
            .title_bar(false)
            .resizable(false)
            .movable(false)
            .frame(frame)
            .anchor(egui::Align2::RIGHT_BOTTOM, [-10.0, -10.0])
            .show(ctx, |ui| {
                ui.horizontal(|ui| {
                    ui.colored_label(
                        LOGO_PURPLE,
                        egui::RichText::new("LOGO DECODED").strong().size(15.0),
                    );
                    ui.separator();
                    ui.colored_label(
                        sc,
                        egui::RichText::new(format!("F\u{22a5} {}", st))
                            .strong()
                            .size(13.0),
                    );
                });
                ui.label(format!(
                    "\u{03bb}\u{2081}={:.4}  \u{03c9}={:.1}  F\u{22a5}\u{221d}{:.4}",
                    gap, omega, thrust
                ));
                dim_label(ui, &format!("{}x{} torus, {} qubits", n, n, n * n));
                dim_label(ui, "Prior art: November 2023");
                if self.paused {
                    ui.colored_label(GOLD_EG, egui::RichText::new("PAUSED").size(11.0));
                }
            });
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Toroidal Engine tab: Sphere rolling INSIDE the torus tube
// ═══════════════════════════════════════════════════════════════════════════════

const TE_ORANGE: egui::Color32 = egui::Color32::from_rgb(255, 160, 60);

/// Compute a point on the tube center line at toroidal angle u.
fn tube_center(r_maj: f32, u: f32) -> [f32; 3] {
    [r_maj * u.cos(), r_maj * u.sin(), 0.0]
}

/// Compute local frame at toroidal angle u on the torus.
/// Returns (tangent, normal_outward, binormal_up) — a right-handed frame.
fn tube_frame(u: f32) -> ([f32; 3], [f32; 3], [f32; 3]) {
    // tangent = d/du of (cos u, sin u, 0) = (-sin u, cos u, 0)
    let tangent = [-u.sin(), u.cos(), 0.0];
    // normal points outward from the torus axis = (cos u, sin u, 0)
    let normal = [u.cos(), u.sin(), 0.0];
    // binormal = tangent × normal = (0, 0, -1) → use (0, 0, 1) for right-hand
    let binormal = [0.0_f32, 0.0, 1.0];
    (tangent, normal, binormal)
}

/// Point inside the tube at toroidal angle u, poloidal angle v, at radius r from tube center.
pub fn tube_interior_pt(r_maj: f32, r_offset: f32, u: f32, v: f32) -> [f32; 3] {
    let (_t, n, b) = tube_frame(u);
    let center = tube_center(r_maj, u);
    [
        center[0] + r_offset * (v.cos() * n[0] + v.sin() * b[0]),
        center[1] + r_offset * (v.cos() * n[1] + v.sin() * b[1]),
        center[2] + r_offset * (v.cos() * n[2] + v.sin() * b[2]),
    ]
}

impl QuantumEngineApp {
    // ─── Controls ───────────────────────────────────────────────────────

    fn draw_te_controls(&mut self, ui: &mut egui::Ui) {
        ui.colored_label(
            LOGO_RED,
            egui::RichText::new("TOROIDAL ENGINE").strong().size(13.0),
        );
        dim_label(ui, "Sphere confined inside torus tube");
        ui.add_space(4.0);

        section_heading(ui, "TORUS GEOMETRY");
        ui.label("Major radius R (tube center path)");
        ui.add(egui::Slider::new(&mut self.te_torus_major, 0.6..=2.0).text("R"));
        ui.label("Minor radius r (tube diameter)");
        ui.add(egui::Slider::new(&mut self.te_torus_minor, 0.15..=0.8).text("r"));
        ui.add_space(2.0);
        let sphere_d = self.te_torus_minor * 2.0;
        dim_label(
            ui,
            &format!("Sphere diameter = tube diameter = {:.2}", sphere_d),
        );
        dim_label(ui, &format!("Sphere radius = {:.3}", self.te_torus_minor));
        ui.add_space(4.0);

        section_heading(ui, "SPHERE MOTION");
        ui.label("Toroidal speed (around tube)");
        ui.add(egui::Slider::new(&mut self.te_sphere_speed, 0.0..=2.0).text("rad/s"));
        ui.label("Sphere self-spin");
        ui.add(egui::Slider::new(&mut self.te_spin_speed, 0.0..=5.0).text("rad/s"));
        ui.add_space(4.0);

        section_heading(ui, "TONNETZ LATTICE");
        let mut n_f = self.te_lattice_n as f64;
        ui.add(
            egui::Slider::new(&mut n_f, 4.0..=24.0)
                .integer()
                .text("N\u{00d7}N"),
        );
        self.te_lattice_n = n_f as usize;
        ui.add_space(4.0);

        section_heading(ui, "OVERLAYS");
        ui.checkbox(&mut self.te_show_force, "Orthogonal force vectors");
        ui.checkbox(&mut self.te_show_tonnetz, "Tonnetz lattice nodes");
        ui.checkbox(&mut self.te_show_trail, "Sphere trail");
        ui.add_space(8.0);

        section_heading(ui, "PHYSICS");
        dim_label(ui, "The sphere rolls inside the");
        dim_label(ui, "toroidal tube. Tube walls confine");
        dim_label(ui, "angular momentum to two modes:");
        ui.add_space(4.0);
        ui.colored_label(LOGO_PURPLE, egui::RichText::new("Toroidal (u)").size(12.0));
        dim_label(ui, "  Around the big loop");
        ui.colored_label(LOGO_CYAN, egui::RichText::new("Poloidal (v)").size(12.0));
        dim_label(ui, "  Around the tube cross-section");
        ui.add_space(4.0);
        ui.colored_label(LOGO_RED, egui::RichText::new("Orthogonal force").size(12.0));
        dim_label(ui, "  Confined toroidal momentum");
        dim_label(ui, "  \u{2192} axial force along z-axis");
        ui.add_space(4.0);
        dim_label(ui, "\u{03c0}\u{2081}(T\u{00b2}) = \u{2124}\u{00d7}\u{2124}");
        dim_label(ui, "Two winding numbers \u{2192}");
        dim_label(ui, "independent angular momenta");
    }

    // ─── Results ────────────────────────────────────────────────────────

    fn draw_te_results(&mut self, ui: &mut egui::Ui) {
        let n = self.te_lattice_n;
        let torus = crate::torus::TorusLattice::new(n, 1.0);
        let gap = torus.spectral_gap();
        let n_q = n * n;

        section_heading(ui, "SPECTRAL GAP");
        ui.colored_label(
            LOGO_PURPLE,
            egui::RichText::new(format!("\u{03bb}\u{2081} = {:.6}", gap))
                .strong()
                .size(16.0),
        );
        dim_label(ui, &format!("{}x{} torus, {} sites", n, n, n_q));
        ui.add_space(4.0);

        // Kinetic energy of sphere (dimensionless)
        let omega_t = self.te_sphere_speed; // toroidal
        let omega_s = self.te_spin_speed; // self-spin
        let r_maj = self.te_torus_major as f64;
        let r_min = self.te_torus_minor as f64;

        // Moment of inertia: solid sphere I = 2/5 m r²
        // Rolling inside tube: v_cm = R * omega_t, v_rot = r * omega_s
        // KE_toroidal = 1/2 m (R * omega_t)²
        // KE_spin = 1/2 * (2/5 m r²) * omega_s²
        let ke_toroidal = 0.5 * r_maj * r_maj * omega_t * omega_t;
        let ke_spin = 0.5 * 0.4 * r_min * r_min * omega_s * omega_s;
        let ke_total = ke_toroidal + ke_spin;

        // Angular momentum: L_toroidal = m R² omega_t (around torus axis)
        let l_toroidal = r_maj * r_maj * omega_t;
        // Angular momentum from spin: L_spin = (2/5) m r² omega_s
        let l_spin = 0.4 * r_min * r_min * omega_s;

        // Orthogonal force: proportional to spectral gap × angular momentum
        let f_ortho = gap * l_toroidal;
        // Coherence-enhanced force: includes spectral gap amplification
        let f_enhanced = gap * (l_toroidal + l_spin);

        section_heading(ui, "KINETIC ENERGY");
        ui.horizontal(|ui| {
            ui.colored_label(LOGO_PURPLE, "KE toroidal:");
            ui.label(format!("{:.4}", ke_toroidal));
        });
        ui.horizontal(|ui| {
            ui.colored_label(LOGO_CYAN, "KE spin:");
            ui.label(format!("{:.4}", ke_spin));
        });
        ui.horizontal(|ui| {
            ui.colored_label(LABEL_CLR, "KE total:");
            ui.label(format!("{:.4}", ke_total));
        });
        ui.add_space(4.0);

        section_heading(ui, "ANGULAR MOMENTUM");
        ui.horizontal(|ui| {
            ui.colored_label(LOGO_PURPLE, "L toroidal:");
            ui.label(format!("{:.4}", l_toroidal));
        });
        ui.horizontal(|ui| {
            ui.colored_label(LOGO_CYAN, "L spin:");
            ui.label(format!("{:.4}", l_spin));
        });
        ui.add_space(4.0);

        section_heading(ui, "ORTHOGONAL FORCE");
        ui.colored_label(
            LOGO_RED,
            egui::RichText::new(format!("F\u{22a5} = {:.4}", f_ortho))
                .strong()
                .size(16.0),
        );
        dim_label(
            ui,
            &format!(
                "\u{03bb}\u{2081} \u{00d7} L_toroidal = {:.4} \u{00d7} {:.4}",
                gap, l_toroidal
            ),
        );
        ui.add_space(4.0);
        ui.colored_label(
            TE_ORANGE,
            egui::RichText::new(format!("F\u{22a5}(enhanced) = {:.4}", f_enhanced))
                .strong()
                .size(14.0),
        );
        dim_label(ui, "Includes spin angular momentum");
        ui.add_space(8.0);

        // Coherence time
        let coherence =
            crate::coherence::coherence_time_normalized(gap, 1.0_f64 / std::f64::consts::E);
        let mixing = torus.mixing_time_lattice();

        section_heading(ui, "COHERENCE");
        ui.horizontal(|ui| {
            ui.colored_label(LOGO_CYAN, "Coherence \u{03c4}/\u{03b3}:");
            ui.label(format!("{:.2}", coherence));
        });
        ui.horizontal(|ui| {
            ui.colored_label(LOGO_CYAN, "Mixing time:");
            ui.label(format!("{:.2}", mixing));
        });
        ui.add_space(8.0);

        section_heading(ui, "SPHERE GEOMETRY");
        dim_label(ui, &format!("Sphere radius: {:.3}", r_min));
        dim_label(ui, &format!("Tube radius: {:.3}", r_min));
        dim_label(ui, &format!("Tube center: R = {:.3}", r_maj));
        dim_label(ui, "Sphere fills tube cross-section");
        dim_label(ui, "(snug fit, no lateral play)");
        ui.add_space(4.0);

        // Current position
        let u_deg = (self.te_sphere_u * 180.0 / PI).rem_euclid(360.0);
        dim_label(ui, &format!("Sphere u = {:.0}\u{00b0}", u_deg));
    }

    // ─── Central panel: 3D torus with sphere INSIDE the tube ────────────

    fn draw_te_central(&mut self, ui: &mut egui::Ui) {
        if !self.paused {
            let dt = ui.input(|i| i.predicted_dt);
            self.te_sphere_u += dt * self.te_sphere_speed as f32;
            self.te_sphere_v += dt * self.te_spin_speed as f32;

            // Record trail
            let sphere_pos = tube_center(self.te_torus_major, self.te_sphere_u);
            self.te_trail.push(sphere_pos);
            if self.te_trail.len() > 512 {
                self.te_trail.remove(0);
            }
        }

        let rect = ui.available_rect_before_wrap();
        let painter = ui.painter_at(rect);
        painter.rect_filled(rect, 0.0, egui::Color32::from_rgb(10, 12, 18));

        let rm = self.te_torus_major;
        let rn = self.te_torus_minor;
        let rot = self.rotation;
        let time = self.time;
        let rings = 24_usize;
        let segs = 48_usize;

        // ── Torus surface (semi-transparent, so you can see the sphere inside) ──
        // We draw the back half first, then the sphere, then the front half
        // For simplicity, draw the whole torus semi-transparent
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
                let alpha = (10.0 + 14.0 * depth_t) as u8; // more transparent to see sphere
                let r = (20.0 + 50.0 * depth_t) as u8;
                let g = (30.0 + 40.0 * depth_t) as u8;
                let b = (60.0 + 70.0 * depth_t) as u8;

                let mesh = egui::Mesh {
                    indices: vec![0, 1, 2, 0, 2, 3],
                    vertices: vec![
                        egui::epaint::Vertex {
                            pos: p00,
                            uv: egui::epaint::WHITE_UV,
                            color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                        },
                        egui::epaint::Vertex {
                            pos: p10,
                            uv: egui::epaint::WHITE_UV,
                            color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                        },
                        egui::epaint::Vertex {
                            pos: p11,
                            uv: egui::epaint::WHITE_UV,
                            color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                        },
                        egui::epaint::Vertex {
                            pos: p01,
                            uv: egui::epaint::WHITE_UV,
                            color: egui::Color32::from_rgba_unmultiplied(r, g, b, alpha),
                        },
                    ],
                    texture_id: egui::TextureId::default(),
                };
                painter.add(egui::Shape::mesh(mesh));
            }
        }

        // ── Torus wireframe ─────────────────────────────────────────────
        for ring in 0..rings {
            let fixed = 2.0 * PI * ring as f32 / rings as f32;
            for s in 0..segs {
                let a = 2.0 * PI * s as f32 / segs as f32;
                let b = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;
                let (s1, z1) = project(torus_pt(rm, rn, fixed, a), rot, rect);
                let (s2, _) = project(torus_pt(rm, rn, fixed, b), rot, rect);
                let al = depth_alpha(z1);
                painter.line_segment(
                    [s1, s2],
                    egui::Stroke::new(
                        0.4,
                        egui::Color32::from_rgba_unmultiplied(60, 80, 140, (al as f32 * 0.5) as u8),
                    ),
                );
                let (s1, z1) = project(torus_pt(rm, rn, a, fixed), rot, rect);
                let (s2, _) = project(torus_pt(rm, rn, b, fixed), rot, rect);
                let al = depth_alpha(z1);
                painter.line_segment(
                    [s1, s2],
                    egui::Stroke::new(
                        0.4,
                        egui::Color32::from_rgba_unmultiplied(60, 80, 140, (al as f32 * 0.5) as u8),
                    ),
                );
            }
        }

        // ── Tonnetz lattice nodes ───────────────────────────────────────
        if self.te_show_tonnetz {
            let grid = self.te_lattice_n;
            for row in 0..grid {
                for col in 0..grid {
                    let u = 2.0 * PI * row as f32 / grid as f32;
                    let v = 2.0 * PI * col as f32 / grid as f32;
                    let (sp, z) = project(torus_pt(rm, rn + 0.015, u, v), rot, rect);
                    let al = depth_alpha(z);
                    let phase_v = 0.5 + 0.5 * (time * 1.5 + u + v).sin();
                    let br = (150.0 * phase_v) as u8;
                    painter.circle_filled(
                        sp,
                        1.8,
                        egui::Color32::from_rgba_unmultiplied(br, br, (br as f32 * 0.7) as u8, al),
                    );
                }
            }
        }

        // ── Sphere trail ────────────────────────────────────────────────
        if self.te_show_trail && self.te_trail.len() > 1 {
            let trail_len = self.te_trail.len();
            let stride = (trail_len / 200).max(1);
            for i in (stride..trail_len).step_by(stride) {
                let (p1, z1) = project(self.te_trail[i - stride], rot, rect);
                let (p2, _) = project(self.te_trail[i], rot, rect);
                let al = depth_alpha(z1);
                let frac = i as f32 / trail_len as f32;
                let r = (255.0 * frac) as u8;
                let g = (140.0 * frac) as u8;
                let b = (60.0 * frac) as u8;
                painter.line_segment(
                    [p1, p2],
                    egui::Stroke::new(
                        2.0,
                        egui::Color32::from_rgba_unmultiplied(r, g, b, (al as f32 * frac) as u8),
                    ),
                );
            }
        }

        // ── THE SPHERE (inside the tube) ────────────────────────────────
        // Sphere center is at tube center line, at current toroidal angle
        let sphere_u = self.te_sphere_u;
        let sphere_center = tube_center(rm, sphere_u);
        let sphere_r = rn * 0.95; // slightly less than tube radius (snug fit)

        // Draw sphere wireframe at tube center position
        let spin_angle = self.te_sphere_v;
        let (_tangent, normal, binormal) = tube_frame(sphere_u);

        // Sphere equator (in the plane perpendicular to the tube tangent)
        let eq_segs = 32_usize;
        for s in 0..eq_segs {
            let t0 = 2.0 * PI * s as f32 / eq_segs as f32;
            let t1 = 2.0 * PI * ((s + 1) % eq_segs) as f32 / eq_segs as f32;

            // Equator in normal-binormal plane (the tube cross-section plane)
            let a0 = t0 + spin_angle;
            let a1 = t1 + spin_angle;
            let eq0 = [
                sphere_center[0] + sphere_r * (a0.cos() * normal[0] + a0.sin() * binormal[0]),
                sphere_center[1] + sphere_r * (a0.cos() * normal[1] + a0.sin() * binormal[1]),
                sphere_center[2] + sphere_r * (a0.cos() * normal[2] + a0.sin() * binormal[2]),
            ];
            let eq1 = [
                sphere_center[0] + sphere_r * (a1.cos() * normal[0] + a1.sin() * binormal[0]),
                sphere_center[1] + sphere_r * (a1.cos() * normal[1] + a1.sin() * binormal[1]),
                sphere_center[2] + sphere_r * (a1.cos() * normal[2] + a1.sin() * binormal[2]),
            ];
            let (pa, za) = project(eq0, rot, rect);
            let (pb, _) = project(eq1, rot, rect);
            let al = depth_alpha(za);
            painter.line_segment(
                [pa, pb],
                egui::Stroke::new(2.0, egui::Color32::from_rgba_unmultiplied(255, 160, 60, al)),
            );
        }

        // Additional meridian circles on the sphere (along the tube direction)
        for m in 0..3 {
            let offset = PI * m as f32 / 3.0 + spin_angle;
            for s in 0..eq_segs {
                let t0 = 2.0 * PI * s as f32 / eq_segs as f32;
                let t1 = 2.0 * PI * ((s + 1) % eq_segs) as f32 / eq_segs as f32;

                // Meridian: rotate around the normal axis
                let tangent = [-sphere_u.sin(), sphere_u.cos(), 0.0_f32];
                let axis_cross = [
                    -offset.sin() * normal[0] + offset.cos() * binormal[0],
                    -offset.sin() * normal[1] + offset.cos() * binormal[1],
                    -offset.sin() * normal[2] + offset.cos() * binormal[2],
                ];
                let m0 = [
                    sphere_center[0]
                        + sphere_r * (t0.cos() * tangent[0] + t0.sin() * axis_cross[0]),
                    sphere_center[1]
                        + sphere_r * (t0.cos() * tangent[1] + t0.sin() * axis_cross[1]),
                    sphere_center[2]
                        + sphere_r * (t0.cos() * tangent[2] + t0.sin() * axis_cross[2]),
                ];
                let m1 = [
                    sphere_center[0]
                        + sphere_r * (t1.cos() * tangent[0] + t1.sin() * axis_cross[0]),
                    sphere_center[1]
                        + sphere_r * (t1.cos() * tangent[1] + t1.sin() * axis_cross[1]),
                    sphere_center[2]
                        + sphere_r * (t1.cos() * tangent[2] + t1.sin() * axis_cross[2]),
                ];
                let (pa, za) = project(m0, rot, rect);
                let (pb, _) = project(m1, rot, rect);
                let al = depth_alpha(za);
                painter.line_segment(
                    [pa, pb],
                    egui::Stroke::new(
                        1.0,
                        egui::Color32::from_rgba_unmultiplied(
                            255,
                            160,
                            60,
                            (al as f32 * 0.6) as u8,
                        ),
                    ),
                );
            }
        }

        // Sphere center dot
        let (sc_pt, _) = project(sphere_center, rot, rect);
        painter.circle_filled(sc_pt, 4.0, TE_ORANGE);

        // ── Orthogonal force arrows ─────────────────────────────────────
        if self.te_show_force {
            let pulse = 0.4 + 0.6 * (time * 2.5).sin().abs();
            let alpha = (200.0 * pulse) as u8;
            let force_color = egui::Color32::from_rgba_unmultiplied(248, 113, 113, alpha);

            // Force along torus symmetry axis (z-axis)
            let tip_height = rn + 0.7;
            let base_height = rn + 0.05;

            let (base_up, _) = project([0.0, 0.0, base_height], rot, rect);
            let (tip_up, _) = project([0.0, 0.0, tip_height], rot, rect);
            painter.line_segment([base_up, tip_up], egui::Stroke::new(4.0, force_color));
            // Arrowhead
            let dx = tip_up.x - base_up.x;
            let dy = tip_up.y - base_up.y;
            let len = (dx * dx + dy * dy).sqrt().max(1.0);
            let ux = dx / len;
            let uy = dy / len;
            let hs = 12.0;
            let h1 = egui::pos2(
                tip_up.x - ux * hs + uy * hs * 0.5,
                tip_up.y - uy * hs - ux * hs * 0.5,
            );
            let h2 = egui::pos2(
                tip_up.x - ux * hs - uy * hs * 0.5,
                tip_up.y - uy * hs + ux * hs * 0.5,
            );
            painter.add(egui::Shape::convex_polygon(
                vec![tip_up, h1, h2],
                force_color,
                egui::Stroke::NONE,
            ));

            let (base_dn, _) = project([0.0, 0.0, -base_height], rot, rect);
            let (tip_dn, _) = project([0.0, 0.0, -tip_height], rot, rect);
            painter.line_segment([base_dn, tip_dn], egui::Stroke::new(4.0, force_color));
            let dx = tip_dn.x - base_dn.x;
            let dy = tip_dn.y - base_dn.y;
            let len = (dx * dx + dy * dy).sqrt().max(1.0);
            let ux = dx / len;
            let uy = dy / len;
            let h1 = egui::pos2(
                tip_dn.x - ux * hs + uy * hs * 0.5,
                tip_dn.y - uy * hs - ux * hs * 0.5,
            );
            let h2 = egui::pos2(
                tip_dn.x - ux * hs - uy * hs * 0.5,
                tip_dn.y - uy * hs + ux * hs * 0.5,
            );
            painter.add(egui::Shape::convex_polygon(
                vec![tip_dn, h1, h2],
                force_color,
                egui::Stroke::NONE,
            ));

            painter.text(
                egui::pos2(tip_up.x + 14.0, tip_up.y),
                egui::Align2::LEFT_CENTER,
                "F\u{22a5}",
                egui::FontId::monospace(14.0),
                LOGO_RED,
            );
            painter.text(
                egui::pos2(tip_dn.x + 14.0, tip_dn.y),
                egui::Align2::LEFT_CENTER,
                "F\u{22a5}",
                egui::FontId::monospace(14.0),
                LOGO_RED,
            );
        }

        // ── Labels ──────────────────────────────────────────────────────
        painter.text(
            egui::pos2(rect.left() + 20.0, rect.top() + 20.0),
            egui::Align2::LEFT_TOP,
            "SPHERE INSIDE TORUS TUBE \u{2192} ORTHOGONAL FORCE",
            egui::FontId::monospace(14.0),
            LOGO_RED,
        );
        painter.text(
            egui::pos2(rect.left() + 20.0, rect.top() + 38.0),
            egui::Align2::LEFT_TOP,
            "Ball confined in toroidal cavity \u{2014} tube diameter = sphere diameter",
            egui::FontId::monospace(11.0),
            DIM,
        );

        // Show sphere position indicator on the tube path
        painter.text(
            egui::pos2(rect.left() + 20.0, rect.top() + 56.0),
            egui::Align2::LEFT_TOP,
            &format!(
                "u = {:.0}\u{00b0}  \u{03c9}_t = {:.2}  \u{03c9}_s = {:.2}",
                (self.te_sphere_u * 180.0 / PI).rem_euclid(360.0),
                self.te_sphere_speed,
                self.te_spin_speed
            ),
            egui::FontId::monospace(11.0),
            TE_ORANGE,
        );

        // Mouse drag
        let resp = ui.interact(rect, egui::Id::new("te_torus_drag"), egui::Sense::drag());
        if resp.dragged() {
            self.rotation[0] += resp.drag_delta().y * 0.01;
            self.rotation[1] += resp.drag_delta().x * 0.01;
        } else if self.auto_rotate && !self.paused {
            self.rotation[1] += 0.003;
        }
    }

    // ─── Status badge ───────────────────────────────────────────────────

    fn draw_te_status(&self, ctx: &egui::Context) {
        let n = self.te_lattice_n;
        let gap = crate::torus::TorusLattice::new(n, 1.0).spectral_gap();
        let r_maj = self.te_torus_major as f64;
        let omega_t = self.te_sphere_speed;
        let l_toroidal = r_maj * r_maj * omega_t;
        let f_ortho = gap * l_toroidal;

        let sc = if f_ortho > 0.3 {
            FOREST_GREEN
        } else if f_ortho > 0.05 {
            GOLD_EG
        } else {
            WARN_RED
        };
        let st = if f_ortho > 0.3 {
            "STRONG"
        } else if f_ortho > 0.05 {
            "MODERATE"
        } else {
            "WEAK"
        };

        let frame = egui::Frame {
            fill: egui::Color32::from_rgba_unmultiplied(18, 12, 12, 230),
            corner_radius: egui::CornerRadius::from(6),
            inner_margin: egui::Margin::same(10),
            stroke: egui::Stroke::new(2.0, LOGO_RED),
            ..Default::default()
        };
        egui::Window::new("te_status")
            .title_bar(false)
            .resizable(false)
            .movable(false)
            .frame(frame)
            .anchor(egui::Align2::RIGHT_BOTTOM, [-10.0, -10.0])
            .show(ctx, |ui| {
                ui.horizontal(|ui| {
                    ui.colored_label(
                        LOGO_RED,
                        egui::RichText::new("TOROIDAL ENGINE").strong().size(15.0),
                    );
                    ui.separator();
                    ui.colored_label(
                        sc,
                        egui::RichText::new(format!("F\u{22a5} {}", st))
                            .strong()
                            .size(13.0),
                    );
                });
                ui.label(format!(
                    "\u{03bb}\u{2081}={:.4}  L={:.4}  F\u{22a5}={:.4}",
                    gap, l_toroidal, f_ortho
                ));
                dim_label(
                    ui,
                    &format!(
                        "{}x{} torus \u{2014} sphere \u{2300}={:.2}",
                        n,
                        n,
                        self.te_torus_minor * 2.0
                    ),
                );
                if self.paused {
                    ui.colored_label(GOLD_EG, egui::RichText::new("PAUSED").size(11.0));
                }
            });
    }
}
