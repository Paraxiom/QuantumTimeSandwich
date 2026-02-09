//! egui UI: sliders, results, labels, and native egui-shape visualization.

use std::f32::consts::PI;

use eframe::egui;
use egui_plot::{Line, Plot, PlotPoints, VLine};

use crate::bridge::{self, ChartData, LatticeSnapshot};
use crate::physics::{PhysicsParams, PhysicsResult};
use crate::worker::{SimRequest, SimResponse, SimWorker};

// ─── Colors ──────────────────────────────────────────────────────────────────

const FOREST_GREEN: egui::Color32 = egui::Color32::from_rgb(106, 154, 106);
const WARN_RED: egui::Color32 = egui::Color32::from_rgb(217, 77, 77);
const DIM: egui::Color32 = egui::Color32::from_rgb(160, 160, 150);
const GOLD_EG: egui::Color32 = egui::Color32::from_rgb(160, 138, 98);
const HEADING_CLR: egui::Color32 = egui::Color32::from_rgb(220, 218, 210);
const LABEL_CLR: egui::Color32 = egui::Color32::from_rgb(230, 228, 218);

// ─── Visuals ─────────────────────────────────────────────────────────────────

fn forest_visuals() -> egui::Visuals {
    let mut vis = egui::Visuals::dark();
    let panel = egui::Color32::from_rgb(32, 38, 32);
    vis.panel_fill = panel;
    vis.window_fill = egui::Color32::from_rgb(36, 42, 36);
    vis.extreme_bg_color = egui::Color32::from_rgb(28, 32, 28);
    vis.faint_bg_color = egui::Color32::from_rgb(40, 50, 40);
    vis.widgets.inactive.bg_fill = egui::Color32::from_rgb(55, 70, 55);
    vis.widgets.hovered.bg_fill = egui::Color32::from_rgb(70, 95, 70);
    vis.widgets.active.bg_fill = FOREST_GREEN;
    vis.override_text_color = Some(LABEL_CLR);
    vis
}

fn dim_label(ui: &mut egui::Ui, text: &str) {
    ui.colored_label(DIM, text);
}

fn section_heading(ui: &mut egui::Ui, text: &str) {
    ui.add_space(4.0);
    ui.colored_label(HEADING_CLR, egui::RichText::new(text).strong().size(14.0));
    ui.separator();
}

// ─── 3-D → 2-D projection helpers ───────────────────────────────────────────

fn torus_pt(r_maj: f32, r_min: f32, u: f32, v: f32) -> [f32; 3] {
    [
        (r_maj + r_min * v.cos()) * u.cos(),
        (r_maj + r_min * v.cos()) * u.sin(),
        r_min * v.sin(),
    ]
}

/// Project a 3-D point to screen space.  Returns (screen_pos, depth_z).
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

fn error_color(has_x: bool, has_z: bool) -> egui::Color32 {
    match (has_x, has_z) {
        (true, true) => egui::Color32::from_rgb(179, 77, 179),
        (true, false) => egui::Color32::from_rgb(217, 77, 77),
        (false, true) => egui::Color32::from_rgb(77, 128, 217),
        _ => egui::Color32::from_rgba_unmultiplied(106, 154, 106, 60),
    }
}

// ─── Draw the rotating torus with non-contractible cycles ────────────────────

fn draw_torus(
    painter: &egui::Painter,
    rect: egui::Rect,
    rot: [f32; 2],
    grid_n: usize,
    snapshot: Option<&LatticeSnapshot>,
    time: f32,
) {
    let rm = 1.2_f32;
    let rn = 0.45_f32;
    let rings = 18_usize;
    let segs = 36_usize;

    // Wireframe rings (u = const and v = const)
    for ring in 0..rings {
        let fixed = 2.0 * PI * ring as f32 / rings as f32;
        for s in 0..segs {
            let a = 2.0 * PI * s as f32 / segs as f32;
            let b = 2.0 * PI * ((s + 1) % segs) as f32 / segs as f32;
            // u-ring
            let (s1, z1) = project(torus_pt(rm, rn, fixed, a), rot, rect);
            let (s2, z2) = project(torus_pt(rm, rn, fixed, b), rot, rect);
            let al = depth_alpha((z1 + z2) * 0.5);
            painter.line_segment(
                [s1, s2],
                egui::Stroke::new(0.7, egui::Color32::from_rgba_unmultiplied(70, 135, 95, al)),
            );
            // v-ring
            let (s1, z1) = project(torus_pt(rm, rn, a, fixed), rot, rect);
            let (s2, z2) = project(torus_pt(rm, rn, b, fixed), rot, rect);
            let al = depth_alpha((z1 + z2) * 0.5);
            painter.line_segment(
                [s1, s2],
                egui::Stroke::new(0.7, egui::Color32::from_rgba_unmultiplied(70, 135, 95, al)),
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
            let r = (160.0 * pulse + 70.0 * (1.0 - pulse)) as u8;
            let g = (138.0 * pulse + 90.0 * (1.0 - pulse)) as u8;
            let bl = (98.0 * pulse + 40.0 * (1.0 - pulse)) as u8;
            painter.line_segment([sc1, sc2], egui::Stroke::new(2.0, egui::Color32::from_rgb(r, g, bl)));
        }
    }

    // Qubit nodes
    for row in 0..grid_n {
        for col in 0..grid_n {
            let u = 2.0 * PI * row as f32 / grid_n as f32;
            let v = 2.0 * PI * col as f32 / grid_n as f32;
            let (sp, z) = project(torus_pt(rm, rn + 0.015, u, v), rot, rect);
            let al = depth_alpha(z);
            let phase = 0.6 + 0.4 * (time * 2.0 + u + v).sin();
            let br = (210.0 * phase) as u8;
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

// ─── Draw the flat toric code lattice ────────────────────────────────────────

fn draw_lattice(painter: &egui::Painter, rect: egui::Rect, snapshot: &LatticeSnapshot) {
    let n = snapshot.n;
    let m = 15.0_f32;
    let inner = egui::Rect::from_min_max(rect.min + egui::vec2(m, m), rect.max - egui::vec2(m, m));
    let sx = inner.width() / n as f32;
    let sy = inner.height() / n as f32;

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

            // Vertex marker
            let is_e = snapshot.e_particles.contains(&(row, col));
            let (vc, vr) = if is_e {
                (egui::Color32::from_rgb(255, 166, 0), 5.0)
            } else {
                (egui::Color32::from_rgb(106, 154, 106), 3.0)
            };
            painter.circle_filled(egui::pos2(x, y), vr, vc);

            // Plaquette marker
            if snapshot.m_particles.contains(&(row, col)) {
                painter.rect_filled(
                    egui::Rect::from_center_size(egui::pos2(x + sx * 0.5, y + sy * 0.5), egui::vec2(7.0, 7.0)),
                    1.0,
                    egui::Color32::from_rgb(217, 77, 77),
                );
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  App state
// ═══════════════════════════════════════════════════════════════════════════════

pub struct ToricDopplerApp {
    params: PhysicsParams,
    lattice_n: usize,
    mc_trials: usize,
    gate_time_ns: f64,
    // Results
    physics_result: Option<PhysicsResult>,
    p_error: f64,
    logical_error_rate: f64,
    logical_failures: usize,
    mc_trials_done: usize,
    // Visualization
    snapshot: Option<LatticeSnapshot>,
    chart_data: Option<ChartData>,
    time: f32,
    rotation: [f32; 2],
    // Worker
    worker: SimWorker,
    needs_eval: bool,
    needs_sweep: bool,
    sweep_pending: bool,
}

impl ToricDopplerApp {
    pub fn new(cc: &eframe::CreationContext<'_>) -> Self {
        cc.egui_ctx.set_visuals(forest_visuals());

        // Explicit font sizes
        let mut style = (*cc.egui_ctx.style()).clone();
        style.text_styles.insert(egui::TextStyle::Heading, egui::FontId::proportional(17.0));
        style.text_styles.insert(egui::TextStyle::Body, egui::FontId::proportional(14.0));
        style.text_styles.insert(egui::TextStyle::Small, egui::FontId::proportional(12.0));
        style.text_styles.insert(egui::TextStyle::Monospace, egui::FontId::monospace(13.0));
        style.text_styles.insert(egui::TextStyle::Button, egui::FontId::proportional(14.0));
        cc.egui_ctx.set_style(style);

        let worker = SimWorker::spawn();
        let mut app = Self {
            params: PhysicsParams::default(),
            lattice_n: 6,
            mc_trials: 500,
            gate_time_ns: bridge::DEFAULT_GATE_TIME_NS,
            physics_result: None,
            p_error: 0.0,
            logical_error_rate: 0.0,
            logical_failures: 0,
            mc_trials_done: 0,
            snapshot: None,
            chart_data: None,
            time: 0.0,
            rotation: [0.3, 0.15],
            worker,
            needs_eval: true,
            needs_sweep: true,
            sweep_pending: false,
        };
        app.send_eval();
        app
    }

    fn send_eval(&mut self) {
        self.worker.send(SimRequest::Evaluate {
            params: self.params.clone(),
            lattice_n: self.lattice_n,
            gate_time_ns: self.gate_time_ns,
            mc_trials: self.mc_trials,
        });
        self.needs_eval = false;
    }

    fn send_sweep(&mut self) {
        self.worker.send(SimRequest::Sweep {
            lattice_n: self.lattice_n,
            mc_trials: (self.mc_trials / 5).max(50),
            operating_p: self.p_error,
        });
        self.needs_sweep = false;
        self.sweep_pending = true;
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Frame update
// ═══════════════════════════════════════════════════════════════════════════════

impl eframe::App for ToricDopplerApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        // Tick animation (slow rotation)
        let dt = ctx.input(|i| i.stable_dt).min(0.05);
        self.time += dt;
        self.rotation[0] += dt * 0.10;   // slow
        self.rotation[1] += dt * 0.05;

        // Poll worker
        while let Some(resp) = self.worker.try_recv() {
            match resp {
                SimResponse::Evaluated { physics, p_error, mc_result, snapshot } => {
                    self.p_error = p_error;
                    self.logical_error_rate = mc_result.logical_error_rate;
                    self.logical_failures = mc_result.logical_failures;
                    self.mc_trials_done = mc_result.trials;
                    self.physics_result = Some(physics);
                    self.snapshot = Some(snapshot);
                    if !self.sweep_pending { self.needs_sweep = true; }
                }
                SimResponse::SweptChart(chart) => {
                    self.chart_data = Some(chart);
                    self.sweep_pending = false;
                }
            }
        }

        // ═════ LEFT PANEL: Controls ═════
        egui::SidePanel::left("controls")
            .min_width(240.0)
            .max_width(300.0)
            .show(ctx, |ui| {
                ui.add_space(4.0);
                ui.colored_label(GOLD_EG, egui::RichText::new("DOPPLER-TORIC SIMULATOR").strong().size(13.0));
                dim_label(ui, "Physical layer \u{2192} logical layer bridge");
                ui.add_space(6.0);

                // Physical layer
                section_heading(ui, "PHYSICAL LAYER: Doppler Cooling");
                dim_label(ui, "CNT optomechanical resonator cooled by laser.");
                let mut changed = false;

                ui.add_space(4.0);
                ui.label("Temperature (K)");
                dim_label(ui, "Bath temperature. Lower = fewer thermal phonons.");
                changed |= ui.add(egui::Slider::new(&mut self.params.temperature, 0.01..=300.0).logarithmic(true)).changed();

                ui.add_space(2.0);
                ui.label("Laser Power (mW)");
                dim_label(ui, "Drives intracavity photon number \u{2192} cooperativity.");
                changed |= ui.add(egui::Slider::new(&mut self.params.laser_power, 0.1..=50.0).logarithmic(true)).changed();

                ui.add_space(2.0);
                ui.label("Detuning (\u{00d7}\u{03c9}_m)");
                dim_label(ui, "Red detuning (-1 = optimal sideband cooling).");
                changed |= ui.add(egui::Slider::new(&mut self.params.detuning, -3.0..=0.0)).changed();

                ui.add_space(2.0);
                ui.label("\u{03ba}/2 (\u{00d7}\u{03c9}_m)");
                dim_label(ui, "Cavity half-linewidth.");
                changed |= ui.add(egui::Slider::new(&mut self.params.kappa, 0.01..=2.0).logarithmic(true)).changed();

                ui.add_space(2.0);
                ui.label("Piezo Voltage (V)");
                dim_label(ui, "Piezoelectric drive near mechanical resonance.");
                changed |= ui.add(egui::Slider::new(&mut self.params.piezo_voltage, 0.0..=10.0)).changed();

                // Tonnetz filter
                section_heading(ui, "TONNETZ COHERENCE FILTER");
                dim_label(ui, "Toroidal topology suppresses dephasing noise.");

                ui.add_space(4.0);
                ui.label("Grid Size (N)");
                dim_label(ui, "N\u{00d7}N Tonnetz torus. Larger \u{2192} stronger suppression.");
                changed |= ui.add(egui::Slider::new(&mut self.params.tonnetz_grid_size, 3..=16)).changed();

                ui.add_space(2.0);
                ui.label("Q Factor");
                dim_label(ui, "Quality factor. Higher = more enhancement.");
                changed |= ui.add(egui::Slider::new(&mut self.params.tonnetz_q, 1.0..=200.0).logarithmic(true)).changed();

                // Toric code
                section_heading(ui, "LOGICAL LAYER: Toric Code");
                dim_label(ui, "Kitaev toric code + greedy decoder.");

                ui.add_space(4.0);
                ui.label("Lattice N");
                dim_label(ui, "N\u{00d7}N torus with 2N\u{00b2} physical qubits.");
                changed |= ui.add(egui::Slider::new(&mut self.lattice_n, 3..=12)).changed();

                ui.add_space(2.0);
                ui.label("MC Trials");
                dim_label(ui, "Monte Carlo error-correction trials.");
                changed |= ui.add(egui::Slider::new(&mut self.mc_trials, 50..=5000).logarithmic(true)).changed();

                ui.add_space(2.0);
                ui.label("Gate Time (ns)");
                dim_label(ui, "p = gate_time / T\u{2082}");
                changed |= ui.add(egui::Slider::new(&mut self.gate_time_ns, 10.0..=1000.0).logarithmic(true)).changed();

                if changed {
                    self.needs_eval = true;
                    self.needs_sweep = true;
                }
                if self.needs_eval { self.send_eval(); }
                if self.needs_sweep && !self.sweep_pending { self.send_sweep(); }

                // Pipeline summary
                ui.add_space(6.0);
                ui.separator();
                dim_label(ui, "PIPELINE:");
                dim_label(ui, "  Temp,Laser \u{2192} Doppler \u{2192} n_final");
                dim_label(ui, "  Tonnetz(\u{03bb}\u{2081},Q) \u{2192} T\u{2082} enhancement");
                dim_label(ui, "  T\u{2082} \u{2192} p = t_gate/T\u{2082}");
                dim_label(ui, "  p \u{2192} Toric code MC \u{2192} P_L");
            });

        // ═════ RIGHT PANEL: Results ═════
        egui::SidePanel::right("results")
            .min_width(210.0)
            .max_width(260.0)
            .show(ctx, |ui| {
                section_heading(ui, "PHYSICS RESULTS");

                if let Some(ref phys) = self.physics_result {
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

                    let t2c = if phys.t2_ns > self.gate_time_ns * 10.0 { FOREST_GREEN } else { WARN_RED };
                    ui.colored_label(t2c, format!("T\u{2082}: {:.0} ns  (with Tonnetz)", phys.t2_ns));
                    dim_label(ui, "  Phase coherence time");
                    ui.label(format!("T\u{2082} bare: {:.0} ns", phys.t2_bare_ns));
                    let imp = phys.t2_ns - phys.t2_bare_ns;
                    let imp_c = if imp > 100.0 { FOREST_GREEN } else { GOLD_EG };
                    ui.colored_label(imp_c, format!("\u{0394}T\u{2082}: +{:.0} ns improvement", imp));
                }

                ui.add_space(6.0);
                section_heading(ui, "ERROR CORRECTION");
                ui.label(format!("p = {:.4}", self.p_error));
                dim_label(ui, "  Physical error rate");

                let margin = 0.09 - self.p_error;
                let mc = if margin > 0.0 { FOREST_GREEN } else { WARN_RED };
                ui.colored_label(mc, format!("Margin: {:.1}%", margin * 100.0));
                if margin > 0.0 {
                    dim_label(ui, "  BELOW threshold \u{2713}");
                } else {
                    ui.colored_label(WARN_RED, "  ABOVE threshold!");
                }
                ui.label(format!("P_L = {:.3}  ({}/{})", self.logical_error_rate, self.logical_failures, self.mc_trials_done));
                dim_label(ui, "  Logical error rate");

                ui.add_space(8.0);
                ui.separator();
                dim_label(ui, "COLOR KEY:");
                ui.colored_label(egui::Color32::from_rgb(217, 77, 77), "  Red = X errors (bit flips)");
                ui.colored_label(egui::Color32::from_rgb(77, 128, 217), "  Blue = Z errors (phase flips)");
                ui.colored_label(egui::Color32::from_rgb(179, 77, 179), "  Purple = Y errors (both)");
                ui.colored_label(egui::Color32::from_rgb(255, 166, 0), "  Orange = e-particles");
                ui.colored_label(FOREST_GREEN, "  Green = clean");
                ui.colored_label(GOLD_EG, "  Gold = non-contractible cycles");
            });

        // ═════ CENTRAL PANEL: Torus + Lattice + Chart ═════
        egui::CentralPanel::default()
            .frame(egui::Frame::NONE.fill(egui::Color32::from_rgb(28, 32, 28)))
            .show(ctx, |ui| {
                let full = ui.available_rect_before_wrap();
                let chart_h = (full.height() * 0.30).max(120.0);
                let top = egui::Rect::from_min_max(full.min, egui::pos2(full.max.x, full.max.y - chart_h));
                let bot = egui::Rect::from_min_max(egui::pos2(full.min.x, full.max.y - chart_h), full.max);
                let mid_x = top.center().x;
                let torus_rect = egui::Rect::from_min_max(top.min, egui::pos2(mid_x, top.max.y));
                let lat_rect = egui::Rect::from_min_max(egui::pos2(mid_x, top.min.y), top.max);

                let painter = ui.painter();

                // Torus label
                painter.text(
                    torus_rect.center_top() + egui::vec2(0.0, 12.0),
                    egui::Align2::CENTER_TOP,
                    format!("3D TORUS (T\u{00b2})  \u{2014}  Tonnetz {0}\u{00d7}{0}", self.params.tonnetz_grid_size),
                    egui::FontId::proportional(13.0),
                    HEADING_CLR,
                );

                // Lattice label
                painter.text(
                    lat_rect.center_top() + egui::vec2(0.0, 12.0),
                    egui::Align2::CENTER_TOP,
                    format!("{0}\u{00d7}{0} TORIC CODE  \u{2014}  Pauli frame snapshot", self.lattice_n),
                    egui::FontId::proportional(13.0),
                    HEADING_CLR,
                );

                // Draw torus
                draw_torus(painter, torus_rect, self.rotation, self.params.tonnetz_grid_size, self.snapshot.as_ref(), self.time);

                // Draw lattice
                if let Some(ref snap) = self.snapshot {
                    draw_lattice(painter, lat_rect, snap);
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
                let chart_ui_rect = ui.allocate_rect(chart_inner, egui::Sense::hover());
                let _ = chart_ui_rect;

                // Use egui_plot for the chart
                ui.allocate_new_ui(egui::UiBuilder::new().max_rect(chart_inner), |ui| {
                    let plot = Plot::new("threshold_chart")
                        .width(chart_inner.width())
                        .height(chart_inner.height())
                        .x_axis_label("p (physical error rate)")
                        .y_axis_label("P_L")
                        .include_x(0.0)
                        .include_x(0.2)
                        .include_y(0.0)
                        .include_y(1.0)
                        .show_axes(true)
                        .allow_zoom(false)
                        .allow_drag(false)
                        .allow_scroll(false);

                    plot.show(ui, |plot_ui| {
                        if let Some(ref cd) = self.chart_data {
                            let colors = [
                                egui::Color32::from_rgb(106, 154, 106),
                                egui::Color32::from_rgb(160, 138, 98),
                                egui::Color32::from_rgb(200, 200, 190),
                                egui::Color32::from_rgb(217, 77, 77),
                            ];
                            for (i, curve) in cd.curves.iter().enumerate() {
                                let pts: PlotPoints = curve.points.iter().map(|&(p, pl)| [p, pl]).collect();
                                let color = colors[i % colors.len()];
                                plot_ui.line(Line::new(pts).color(color).width(1.5).name(format!("N={}", curve.n)));
                            }
                        }
                        // Operating point
                        if self.p_error > 0.0 {
                            plot_ui.vline(VLine::new(self.p_error).color(egui::Color32::WHITE).width(1.5));
                        }
                        // Threshold reference
                        plot_ui.vline(VLine::new(0.09).color(egui::Color32::from_rgba_unmultiplied(217, 77, 77, 100)).width(1.0));
                    });
                });
            });

        // Status badge (bottom-right)
        if let Some(ref phys) = self.physics_result {
            let (st, sc) = if self.p_error < 0.09 {
                ("CORRECTABLE", FOREST_GREEN)
            } else {
                ("TOO NOISY", WARN_RED)
            };
            let frame = egui::Frame {
                fill: egui::Color32::from_rgba_unmultiplied(30, 38, 30, 220),
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
                    ui.label(format!("T\u{2082}={:.0}ns  p={:.4}  P_L={:.3}", phys.t2_ns, self.p_error, self.logical_error_rate));
                    dim_label(ui, &format!("Tonnetz: +{:.0}ns ({:.0}\u{00d7})", phys.t2_ns - phys.t2_bare_ns, phys.tonnetz_enhancement));
                });
        }

        ctx.request_repaint();
    }
}
