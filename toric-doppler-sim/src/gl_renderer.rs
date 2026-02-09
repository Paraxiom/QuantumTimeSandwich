//! Raw OpenGL rendering: shaders, VBOs, lattice + torus + chart.

use glow::HasContext;
use std::f32::consts::PI;
use std::num::NonZeroU32;

use crate::bridge::{ChartData, LatticeSnapshot};

// Forest palette colors
const GREEN: [f32; 4] = [0.416, 0.604, 0.416, 1.0];
const GOLD: [f32; 4] = [0.627, 0.541, 0.384, 1.0];
const TEXT_CLR: [f32; 4] = [0.855, 0.843, 0.804, 1.0];
const X_ERR: [f32; 4] = [0.85, 0.3, 0.3, 1.0];
const Z_ERR: [f32; 4] = [0.3, 0.5, 0.85, 1.0];
const XZ_ERR: [f32; 4] = [0.7, 0.3, 0.7, 1.0];
const E_PARTICLE: [f32; 4] = [1.0, 0.65, 0.0, 1.0];
const M_PARTICLE: [f32; 4] = [0.85, 0.3, 0.3, 0.6];
const CLEAN: [f32; 4] = [0.416, 0.604, 0.416, 0.8];

// --- Basic shader (lattice + chart) ---

const VERT_SHADER: &str = r#"#version 330 core
layout(location = 0) in vec3 a_pos;
layout(location = 1) in vec4 a_color;
uniform mat4 u_projection;
uniform float u_point_size;
out vec4 v_color;
void main() {
    gl_Position = u_projection * vec4(a_pos, 1.0);
    gl_PointSize = u_point_size;
    v_color = a_color;
}
"#;

const FRAG_SHADER: &str = r#"#version 330 core
in vec4 v_color;
out vec4 fragColor;
void main() {
    fragColor = v_color;
}
"#;

// --- Torus shader with time-based effects ---

const TORUS_VERT: &str = r#"#version 330 core
layout(location = 0) in vec3 a_pos;
layout(location = 1) in vec4 a_color;
layout(location = 2) in vec2 a_uv;    // (u, v) parametric coords on torus
layout(location = 3) in float a_kind;  // 0=wireframe, 1=cycle1, 2=cycle2, 3=qubit, 4=error

uniform mat4 u_projection;
uniform float u_time;
uniform float u_point_size;
uniform float u_breathe;  // minor radius oscillation

out vec4 v_color;
out vec3 v_pos;
out vec2 v_uv;
flat out float v_kind;

void main() {
    vec3 pos = a_pos;

    // Breathing: displace along normal (radial from tube center)
    float tube_cx = (a_pos.x / max(length(vec2(a_pos.x, a_pos.y)), 0.001));
    float tube_cy = (a_pos.y / max(length(vec2(a_pos.x, a_pos.y)), 0.001));
    vec3 normal = vec3(
        pos.x - 1.2 * tube_cx,
        pos.y - 1.2 * tube_cy,
        pos.z
    );
    normal = normalize(normal);
    pos += normal * u_breathe * 0.03 * sin(u_time * 0.8);

    gl_Position = u_projection * vec4(pos, 1.0);
    gl_PointSize = u_point_size;
    v_color = a_color;
    v_pos = pos;
    v_uv = a_uv;
    v_kind = a_kind;
}
"#;

const TORUS_FRAG: &str = r#"#version 330 core
in vec4 v_color;
in vec3 v_pos;
in vec2 v_uv;
flat in float v_kind;

uniform float u_time;
uniform float u_error_rate; // 0..1, drives visual intensity

out vec4 fragColor;

void main() {
    vec4 c = v_color;
    float kind = v_kind;

    // --- Wireframe: depth fog + shimmer ---
    if (kind < 0.5) {
        // Depth-based fog: fade far-side lines
        float depth = clamp((v_pos.z + 0.5) / 1.0, 0.0, 1.0);
        float fog = 0.08 + 0.22 * depth;

        // Iridescent shimmer: hue shift based on viewing angle approximation
        float angle = atan(v_pos.y, v_pos.x);
        float shimmer = 0.5 + 0.5 * sin(angle * 3.0 + u_time * 1.5);

        // Blend green → cyan → blue based on shimmer
        vec3 col_a = vec3(0.3, 0.6, 0.4);   // forest green
        vec3 col_b = vec3(0.25, 0.55, 0.7);  // teal
        vec3 wire_col = mix(col_a, col_b, shimmer * 0.4);

        c = vec4(wire_col, fog);
    }
    // --- Non-contractible cycle 1 (around tube): flowing energy pulse ---
    else if (kind < 1.5) {
        float pulse = sin(v_uv.y * 6.2832 - u_time * 3.0);
        float glow = 0.5 + 0.5 * pulse;
        float brightness = 0.6 + 0.4 * glow;

        // Gold → white pulse
        vec3 base = vec3(0.627, 0.541, 0.384);
        vec3 hot = vec3(1.0, 0.95, 0.8);
        vec3 col = mix(base, hot, glow * 0.6);

        // Additive glow halo
        float halo = exp(-2.0 * (1.0 - glow));
        col += vec3(0.3, 0.2, 0.05) * halo;

        c = vec4(col, brightness);
    }
    // --- Non-contractible cycle 2 (around hole): counter-rotating pulse ---
    else if (kind < 2.5) {
        float pulse = sin(v_uv.x * 6.2832 + u_time * 2.0);
        float glow = 0.5 + 0.5 * pulse;
        float brightness = 0.6 + 0.4 * glow;

        vec3 base = vec3(0.627, 0.541, 0.384);
        vec3 hot = vec3(1.0, 0.9, 0.7);
        vec3 col = mix(base, hot, glow * 0.6);

        float halo = exp(-2.0 * (1.0 - glow));
        col += vec3(0.25, 0.15, 0.05) * halo;

        c = vec4(col, brightness);
    }
    // --- Qubit nodes: pulsing glow ---
    else if (kind < 3.5) {
        // Each qubit pulses at slightly different phase based on UV
        float phase = v_uv.x * 2.0 + v_uv.y * 3.0;
        float pulse = 0.6 + 0.4 * sin(u_time * 2.5 + phase);

        // Round point shape (discard corners for circles)
        vec2 pc = gl_PointCoord * 2.0 - 1.0;
        float dist = dot(pc, pc);
        if (dist > 1.0) discard;

        // Inner glow
        float inner_glow = exp(-3.0 * dist);

        vec3 core_col = vec3(0.85, 0.84, 0.80); // off-white
        vec3 glow_col = vec3(0.4, 0.8, 0.5);     // green glow
        vec3 col = mix(glow_col, core_col, inner_glow) * pulse;

        // Error rate tints qubits red
        col = mix(col, vec3(0.9, 0.3, 0.2), u_error_rate * 0.5);

        c = vec4(col, pulse * inner_glow + 0.3);
    }
    // --- Error arcs on torus surface ---
    else {
        // Bright animated error chains
        float pulse = 0.7 + 0.3 * sin(u_time * 5.0 + v_uv.x * 12.0);
        c.rgb *= pulse;
        c.a = 0.9;
    }

    fragColor = c;
}
"#;

/// Vertex: position (x, y, z) + color (r, g, b, a) + uv (u, v) + kind.
#[repr(C)]
#[derive(Copy, Clone)]
struct Vertex {
    pos: [f32; 3],
    color: [f32; 4],
}

/// Extended vertex for torus with parametric UV and element kind.
#[repr(C)]
#[derive(Copy, Clone)]
struct TorusVertex {
    pos: [f32; 3],
    color: [f32; 4],
    uv: [f32; 2],
    kind: f32,
}

pub struct GlRenderer {
    // Basic shader (lattice + chart)
    program: glow::Program,
    // Torus shader
    torus_program: glow::Program,
    // Lattice
    lattice_vao: glow::VertexArray,
    lattice_vbo: glow::Buffer,
    lattice_vertex_count: i32,
    lattice_point_start: i32,
    lattice_point_count: i32,
    // Torus
    torus_vao: glow::VertexArray,
    torus_vbo: glow::Buffer,
    torus_line_count: i32,
    torus_point_start: i32,
    torus_point_count: i32,
    torus_total: i32,
    // Chart
    chart_vao: glow::VertexArray,
    chart_vbo: glow::Buffer,
    chart_vertex_count: i32,
    // Animation state
    time: f32,
    rotation: [f32; 2],
    // Current state for dynamic rebuild
    grid_n: usize,
    error_rate: f32,
    snapshot_errors: Option<TorusErrors>,
}

/// Errors mapped onto the torus for visual overlay.
#[derive(Clone)]
struct TorusErrors {
    x_errors: Vec<bool>,
    z_errors: Vec<bool>,
    n: usize,
}

impl GlRenderer {
    pub fn new(gl: &glow::Context) -> Self {
        unsafe {
            let program = create_program(gl, VERT_SHADER, FRAG_SHADER);
            let torus_program = create_program(gl, TORUS_VERT, TORUS_FRAG);

            // Lattice VAO/VBO
            let lattice_vao = gl.create_vertex_array().unwrap();
            let lattice_vbo = gl.create_buffer().unwrap();
            setup_basic_vao(gl, lattice_vao, lattice_vbo);

            // Torus VAO/VBO (extended vertex format)
            let torus_vao = gl.create_vertex_array().unwrap();
            let torus_vbo = gl.create_buffer().unwrap();
            setup_torus_vao(gl, torus_vao, torus_vbo);

            // Chart VAO/VBO
            let chart_vao = gl.create_vertex_array().unwrap();
            let chart_vbo = gl.create_buffer().unwrap();
            setup_basic_vao(gl, chart_vao, chart_vbo);

            let mut renderer = Self {
                program,
                torus_program,
                lattice_vao,
                lattice_vbo,
                lattice_vertex_count: 0,
                lattice_point_start: 0,
                lattice_point_count: 0,
                torus_vao,
                torus_vbo,
                torus_line_count: 0,
                torus_point_start: 0,
                torus_point_count: 0,
                torus_total: 0,
                chart_vao,
                chart_vbo,
                chart_vertex_count: 0,
                time: 0.0,
                rotation: [0.0, 0.0],
                grid_n: 6,
                error_rate: 0.0,
                snapshot_errors: None,
            };
            renderer.rebuild_torus(gl);
            renderer
        }
    }

    /// Set the torus grid size and trigger rebuild.
    pub fn set_grid_n(&mut self, gl: &glow::Context, n: usize) {
        if n != self.grid_n {
            self.grid_n = n;
            self.rebuild_torus(gl);
        }
    }

    /// Set the current error rate for visual feedback.
    pub fn set_error_rate(&mut self, rate: f32) {
        self.error_rate = rate;
    }

    /// Update snapshot errors to overlay on torus.
    pub fn set_snapshot_errors(&mut self, snapshot: &LatticeSnapshot) {
        self.snapshot_errors = Some(TorusErrors {
            x_errors: snapshot.x_errors.clone(),
            z_errors: snapshot.z_errors.clone(),
            n: snapshot.n,
        });
    }

    /// Rebuild the torus mesh (called when grid_n changes or each frame for animation).
    fn rebuild_torus(&mut self, gl: &glow::Context) {
        let mut verts: Vec<TorusVertex> = Vec::new();
        let n = self.grid_n;
        let r_major: f32 = 1.2;
        let r_minor: f32 = 0.45;
        let segments = 64usize;

        // === Wireframe rings (u = const) — kind 0 ===
        let wire_rings = 32usize;
        for i in 0..wire_rings {
            let u = 2.0 * PI * i as f32 / wire_rings as f32;
            let u_norm = i as f32 / wire_rings as f32;
            for j in 0..segments {
                let v1 = 2.0 * PI * j as f32 / segments as f32;
                let v2 = 2.0 * PI * ((j + 1) % segments) as f32 / segments as f32;
                let v1_norm = j as f32 / segments as f32;
                let v2_norm = ((j + 1) % segments) as f32 / segments as f32;
                let p1 = torus_point(r_major, r_minor, u, v1);
                let p2 = torus_point(r_major, r_minor, u, v2);
                verts.push(TorusVertex { pos: p1, color: GREEN, uv: [u_norm, v1_norm], kind: 0.0 });
                verts.push(TorusVertex { pos: p2, color: GREEN, uv: [u_norm, v2_norm], kind: 0.0 });
            }
        }

        // === Wireframe rings (v = const) — kind 0 ===
        for j in 0..wire_rings {
            let v = 2.0 * PI * j as f32 / wire_rings as f32;
            let v_norm = j as f32 / wire_rings as f32;
            for i in 0..segments {
                let u1 = 2.0 * PI * i as f32 / segments as f32;
                let u2 = 2.0 * PI * ((i + 1) % segments) as f32 / segments as f32;
                let u1_norm = i as f32 / segments as f32;
                let u2_norm = ((i + 1) % segments) as f32 / segments as f32;
                let p1 = torus_point(r_major, r_minor, u1, v);
                let p2 = torus_point(r_major, r_minor, u2, v);
                verts.push(TorusVertex { pos: p1, color: GREEN, uv: [u1_norm, v_norm], kind: 0.0 });
                verts.push(TorusVertex { pos: p2, color: GREEN, uv: [u2_norm, v_norm], kind: 0.0 });
            }
        }

        // === Non-contractible cycle 1 (around tube, u=0, vary v) — kind 1 ===
        for j in 0..segments {
            let v1 = 2.0 * PI * j as f32 / segments as f32;
            let v2 = 2.0 * PI * ((j + 1) % segments) as f32 / segments as f32;
            let v1n = j as f32 / segments as f32;
            let v2n = ((j + 1) % segments) as f32 / segments as f32;
            let p1 = torus_point(r_major, r_minor, 0.0, v1);
            let p2 = torus_point(r_major, r_minor, 0.0, v2);
            verts.push(TorusVertex { pos: p1, color: GOLD, uv: [0.0, v1n], kind: 1.0 });
            verts.push(TorusVertex { pos: p2, color: GOLD, uv: [0.0, v2n], kind: 1.0 });
        }

        // === Non-contractible cycle 2 (around hole, v=0, vary u) — kind 2 ===
        for i in 0..segments {
            let u1 = 2.0 * PI * i as f32 / segments as f32;
            let u2 = 2.0 * PI * ((i + 1) % segments) as f32 / segments as f32;
            let u1n = i as f32 / segments as f32;
            let u2n = ((i + 1) % segments) as f32 / segments as f32;
            let p1 = torus_point(r_major, r_minor, u1, 0.0);
            let p2 = torus_point(r_major, r_minor, u2, 0.0);
            verts.push(TorusVertex { pos: p1, color: GOLD, uv: [u1n, 0.0], kind: 2.0 });
            verts.push(TorusVertex { pos: p2, color: GOLD, uv: [u2n, 0.0], kind: 2.0 });
        }

        // === Second pair of non-contractible cycles at offset (PI offset) ===
        // Cycle 1b at u = PI
        for j in 0..segments {
            let v1 = 2.0 * PI * j as f32 / segments as f32;
            let v2 = 2.0 * PI * ((j + 1) % segments) as f32 / segments as f32;
            let v1n = j as f32 / segments as f32;
            let v2n = ((j + 1) % segments) as f32 / segments as f32;
            let p1 = torus_point(r_major, r_minor, PI, v1);
            let p2 = torus_point(r_major, r_minor, PI, v2);
            verts.push(TorusVertex { pos: p1, color: GOLD, uv: [0.5, v1n], kind: 1.0 });
            verts.push(TorusVertex { pos: p2, color: GOLD, uv: [0.5, v2n], kind: 1.0 });
        }
        // Cycle 2b at v = PI
        for i in 0..segments {
            let u1 = 2.0 * PI * i as f32 / segments as f32;
            let u2 = 2.0 * PI * ((i + 1) % segments) as f32 / segments as f32;
            let u1n = i as f32 / segments as f32;
            let u2n = ((i + 1) % segments) as f32 / segments as f32;
            let p1 = torus_point(r_major, r_minor, u1, PI);
            let p2 = torus_point(r_major, r_minor, u2, PI);
            verts.push(TorusVertex { pos: p1, color: GOLD, uv: [u1n, 0.5], kind: 2.0 });
            verts.push(TorusVertex { pos: p2, color: GOLD, uv: [u2n, 0.5], kind: 2.0 });
        }

        // === Error arcs on torus surface — kind 4 ===
        if let Some(ref errs) = self.snapshot_errors {
            let en = errs.n;
            for row in 0..en {
                for col in 0..en {
                    let h_idx = row * en + col;
                    let has_x = errs.x_errors.get(h_idx).copied().unwrap_or(false);
                    let has_z = errs.z_errors.get(h_idx).copied().unwrap_or(false);
                    if has_x || has_z {
                        let color = error_color(has_x, has_z);
                        let u1 = 2.0 * PI * col as f32 / en as f32;
                        let u2 = 2.0 * PI * ((col + 1) % en) as f32 / en as f32;
                        let v = 2.0 * PI * row as f32 / en as f32;
                        let u1n = col as f32 / en as f32;
                        let u2n = ((col + 1) % en) as f32 / en as f32;
                        let vn = row as f32 / en as f32;
                        // Draw error arc with slight offset outward
                        let p1 = torus_point(r_major, r_minor + 0.02, u1, v);
                        let p2 = torus_point(r_major, r_minor + 0.02, u2, v);
                        verts.push(TorusVertex { pos: p1, color, uv: [u1n, vn], kind: 4.0 });
                        verts.push(TorusVertex { pos: p2, color, uv: [u2n, vn], kind: 4.0 });
                    }

                    let v_idx = en * en + row * en + col;
                    let has_x = errs.x_errors.get(v_idx).copied().unwrap_or(false);
                    let has_z = errs.z_errors.get(v_idx).copied().unwrap_or(false);
                    if has_x || has_z {
                        let color = error_color(has_x, has_z);
                        let u = 2.0 * PI * col as f32 / en as f32;
                        let v1 = 2.0 * PI * row as f32 / en as f32;
                        let v2 = 2.0 * PI * ((row + 1) % en) as f32 / en as f32;
                        let un = col as f32 / en as f32;
                        let v1n = row as f32 / en as f32;
                        let v2n = ((row + 1) % en) as f32 / en as f32;
                        let p1 = torus_point(r_major, r_minor + 0.02, u, v1);
                        let p2 = torus_point(r_major, r_minor + 0.02, u, v2);
                        verts.push(TorusVertex { pos: p1, color, uv: [un, v1n], kind: 4.0 });
                        verts.push(TorusVertex { pos: p2, color, uv: [un, v2n], kind: 4.0 });
                    }
                }
            }
        }

        let line_count = verts.len() as i32;

        // === Qubit nodes on torus surface — kind 3 (drawn as POINTS) ===
        for row in 0..n {
            for col in 0..n {
                let u = 2.0 * PI * row as f32 / n as f32;
                let v = 2.0 * PI * col as f32 / n as f32;
                let p = torus_point(r_major, r_minor + 0.01, u, v);
                let u_norm = row as f32 / n as f32;
                let v_norm = col as f32 / n as f32;
                verts.push(TorusVertex { pos: p, color: TEXT_CLR, uv: [u_norm, v_norm], kind: 3.0 });
            }
        }

        let point_count = verts.len() as i32 - line_count;

        self.torus_line_count = line_count;
        self.torus_point_start = line_count;
        self.torus_point_count = point_count;
        self.torus_total = verts.len() as i32;

        upload_torus_vertices(gl, self.torus_vao, self.torus_vbo, &verts);
    }

    /// Rebuild the lattice visualization from a snapshot.
    pub fn update_lattice(&mut self, gl: &glow::Context, snapshot: &LatticeSnapshot) {
        let n = snapshot.n;
        let mut verts: Vec<Vertex> = Vec::new();

        let spacing = 2.0 / (n as f32 + 1.0);
        let offset = -1.0 + spacing;

        for row in 0..n {
            for col in 0..n {
                let x = offset + col as f32 * spacing;
                let y = offset + row as f32 * spacing;

                let h_idx = row * n + col;
                let h_has_x = snapshot.x_errors.get(h_idx).copied().unwrap_or(false);
                let h_has_z = snapshot.z_errors.get(h_idx).copied().unwrap_or(false);
                let h_color = error_color(h_has_x, h_has_z);

                let x2_draw = if col + 1 < n {
                    offset + (col + 1) as f32 * spacing
                } else {
                    offset + n as f32 * spacing
                };
                verts.push(Vertex { pos: [x, y, 0.0], color: h_color });
                verts.push(Vertex { pos: [x2_draw, y, 0.0], color: h_color });

                let v_idx = n * n + row * n + col;
                let v_has_x = snapshot.x_errors.get(v_idx).copied().unwrap_or(false);
                let v_has_z = snapshot.z_errors.get(v_idx).copied().unwrap_or(false);
                let v_color = error_color(v_has_x, v_has_z);

                let y2_draw = if row + 1 < n {
                    offset + (row + 1) as f32 * spacing
                } else {
                    offset + n as f32 * spacing
                };
                verts.push(Vertex { pos: [x, y, 0.0], color: v_color });
                verts.push(Vertex { pos: [x, y2_draw, 0.0], color: v_color });
            }
        }

        let line_count = verts.len() as i32;

        for row in 0..n {
            for col in 0..n {
                let x = offset + col as f32 * spacing;
                let y = offset + row as f32 * spacing;
                let is_e = snapshot.e_particles.contains(&(row, col));
                let color = if is_e { E_PARTICLE } else { CLEAN };
                verts.push(Vertex { pos: [x, y, 0.0], color });
            }
        }

        for row in 0..n {
            for col in 0..n {
                let x = offset + col as f32 * spacing + spacing * 0.5;
                let y = offset + row as f32 * spacing + spacing * 0.5;
                let is_m = snapshot.m_particles.contains(&(row, col));
                if is_m {
                    verts.push(Vertex { pos: [x, y, 0.0], color: M_PARTICLE });
                }
            }
        }

        let point_count = verts.len() as i32 - line_count;

        self.lattice_vertex_count = line_count;
        self.lattice_point_start = line_count;
        self.lattice_point_count = point_count;

        upload_basic_vertices(gl, self.lattice_vao, self.lattice_vbo, &verts);

        // Also update the torus error overlay
        self.set_snapshot_errors(snapshot);
        self.rebuild_torus(gl);
    }

    /// Update chart data for threshold curves.
    pub fn update_charts(&mut self, gl: &glow::Context, data: &ChartData) {
        let mut verts: Vec<Vertex> = Vec::new();
        let colors = [GREEN, GOLD, TEXT_CLR, X_ERR];

        verts.push(Vertex { pos: [-0.9, -0.9, 0.0], color: [0.4, 0.4, 0.4, 0.5] });
        verts.push(Vertex { pos: [0.9, -0.9, 0.0], color: [0.4, 0.4, 0.4, 0.5] });
        verts.push(Vertex { pos: [-0.9, -0.9, 0.0], color: [0.4, 0.4, 0.4, 0.5] });
        verts.push(Vertex { pos: [-0.9, 0.9, 0.0], color: [0.4, 0.4, 0.4, 0.5] });

        for i in 1..=4 {
            let x = -0.9 + i as f32 * 0.45;
            verts.push(Vertex { pos: [x, -0.9, 0.0], color: [0.3, 0.3, 0.3, 0.2] });
            verts.push(Vertex { pos: [x, 0.9, 0.0], color: [0.3, 0.3, 0.3, 0.2] });
        }
        for i in 1..=4 {
            let y = -0.9 + i as f32 * 0.45;
            verts.push(Vertex { pos: [-0.9, y, 0.0], color: [0.3, 0.3, 0.3, 0.2] });
            verts.push(Vertex { pos: [0.9, y, 0.0], color: [0.3, 0.3, 0.3, 0.2] });
        }

        for (ci, curve) in data.curves.iter().enumerate() {
            let color = colors[ci % colors.len()];
            for window in curve.points.windows(2) {
                let (p1, pl1) = window[0];
                let (p2, pl2) = window[1];
                let x1 = -0.9 + (p1 / 0.2) as f32 * 1.8;
                let y1 = -0.9 + pl1 as f32 * 1.8;
                let x2 = -0.9 + (p2 / 0.2) as f32 * 1.8;
                let y2 = -0.9 + pl2 as f32 * 1.8;
                verts.push(Vertex { pos: [x1, y1, 0.0], color });
                verts.push(Vertex { pos: [x2, y2, 0.0], color });
            }
        }

        if data.operating_p > 0.0 {
            let x = -0.9 + (data.operating_p / 0.2) as f32 * 1.8;
            let op_color = [1.0, 1.0, 1.0, 0.6];
            verts.push(Vertex { pos: [x, -0.9, 0.0], color: op_color });
            verts.push(Vertex { pos: [x, 0.9, 0.0], color: op_color });
        }

        self.chart_vertex_count = verts.len() as i32;
        upload_basic_vertices(gl, self.chart_vao, self.chart_vbo, &verts);
    }

    /// Render all GL content.
    pub fn render(&mut self, gl: &glow::Context, viewport: [f32; 4], dt: f32) {
        self.time += dt;
        self.rotation[0] += dt * 0.3;
        self.rotation[1] += dt * 0.15;

        unsafe {
            // ===== Save GL state so egui text rendering survives =====
            let prev_program = gl.get_parameter_i32(glow::CURRENT_PROGRAM) as u32;
            let prev_vao = gl.get_parameter_i32(0x85B5 /* VERTEX_ARRAY_BINDING */) as u32;
            let prev_buf = gl.get_parameter_i32(0x8894 /* ARRAY_BUFFER_BINDING */) as u32;
            let prev_active_tex = gl.get_parameter_i32(glow::ACTIVE_TEXTURE) as u32;
            let prev_texture = gl.get_parameter_i32(glow::TEXTURE_BINDING_2D) as u32;
            let prev_blend = gl.is_enabled(glow::BLEND);
            let prev_scissor = gl.is_enabled(glow::SCISSOR_TEST);

            // Set up our rendering state
            gl.enable(glow::BLEND);
            gl.blend_func(glow::SRC_ALPHA, glow::ONE_MINUS_SRC_ALPHA);
            gl.enable(glow::PROGRAM_POINT_SIZE);
            gl.enable(glow::LINE_SMOOTH);
            gl.disable(glow::SCISSOR_TEST);

            let vp_x = viewport[0] as i32;
            let vp_y = viewport[1] as i32;
            let vp_w = viewport[2] as i32;
            let vp_h = viewport[3] as i32;

            // === Torus (left half) — uses torus_program ===
            let torus_w = vp_w / 2;
            let torus_h = vp_h * 2 / 3;
            gl.viewport(vp_x, vp_y + vp_h - torus_h, torus_w, torus_h);

            gl.use_program(Some(self.torus_program));

            let proj = rotation_projection(
                self.rotation[0],
                self.rotation[1],
                torus_w as f32 / torus_h.max(1) as f32,
            );
            set_uniform_mat4(gl, self.torus_program, "u_projection", &proj);
            set_uniform_f32(gl, self.torus_program, "u_time", self.time);
            set_uniform_f32(gl, self.torus_program, "u_point_size", 8.0);
            set_uniform_f32(gl, self.torus_program, "u_breathe", 1.0);
            set_uniform_f32(gl, self.torus_program, "u_error_rate", self.error_rate);

            gl.line_width(1.0);
            gl.bind_vertex_array(Some(self.torus_vao));

            // Draw wireframe + cycles + error arcs as LINES
            if self.torus_line_count > 0 {
                gl.draw_arrays(glow::LINES, 0, self.torus_line_count);
            }

            // Draw qubit nodes as POINTS
            if self.torus_point_count > 0 {
                set_uniform_f32(gl, self.torus_program, "u_point_size", 10.0);
                gl.draw_arrays(glow::POINTS, self.torus_point_start, self.torus_point_count);
            }

            // === Lattice (right half) — uses basic program ===
            gl.use_program(Some(self.program));

            let lattice_w = vp_w - torus_w;
            let lattice_h = torus_h;
            gl.viewport(vp_x + torus_w, vp_y + vp_h - lattice_h, lattice_w, lattice_h);

            let ortho = ortho_projection(lattice_w as f32 / lattice_h.max(1) as f32);
            set_uniform_mat4(gl, self.program, "u_projection", &ortho);
            set_uniform_f32(gl, self.program, "u_point_size", 10.0);

            gl.bind_vertex_array(Some(self.lattice_vao));
            if self.lattice_vertex_count > 0 {
                gl.draw_arrays(glow::LINES, 0, self.lattice_vertex_count);
            }
            if self.lattice_point_count > 0 {
                set_uniform_f32(gl, self.program, "u_point_size", 12.0);
                gl.draw_arrays(glow::POINTS, self.lattice_point_start, self.lattice_point_count);
            }

            // === Chart (bottom strip) ===
            let chart_h = vp_h - torus_h;
            if chart_h > 20 {
                gl.viewport(vp_x, vp_y, vp_w, chart_h);

                let chart_ortho = ortho_projection(vp_w as f32 / chart_h.max(1) as f32);
                set_uniform_mat4(gl, self.program, "u_projection", &chart_ortho);
                set_uniform_f32(gl, self.program, "u_point_size", 4.0);

                gl.bind_vertex_array(Some(self.chart_vao));
                if self.chart_vertex_count > 0 {
                    gl.draw_arrays(glow::LINES, 0, self.chart_vertex_count);
                }
            }

            // ===== Restore GL state for egui =====
            // Shader program
            if let Some(p) = NonZeroU32::new(prev_program) {
                gl.use_program(Some(glow::NativeProgram(p)));
            } else {
                gl.use_program(None);
            }
            // Vertex array
            if let Some(v) = NonZeroU32::new(prev_vao) {
                gl.bind_vertex_array(Some(glow::NativeVertexArray(v)));
            } else {
                gl.bind_vertex_array(None);
            }
            // Array buffer
            if let Some(b) = NonZeroU32::new(prev_buf) {
                gl.bind_buffer(glow::ARRAY_BUFFER, Some(glow::NativeBuffer(b)));
            } else {
                gl.bind_buffer(glow::ARRAY_BUFFER, None);
            }
            // Texture
            gl.active_texture(prev_active_tex);
            if let Some(t) = NonZeroU32::new(prev_texture) {
                gl.bind_texture(glow::TEXTURE_2D, Some(glow::NativeTexture(t)));
            } else {
                gl.bind_texture(glow::TEXTURE_2D, None);
            }
            // Enable/disable flags
            if prev_blend { gl.enable(glow::BLEND); } else { gl.disable(glow::BLEND); }
            if prev_scissor { gl.enable(glow::SCISSOR_TEST); } else { gl.disable(glow::SCISSOR_TEST); }
            gl.disable(glow::LINE_SMOOTH);
            gl.disable(glow::PROGRAM_POINT_SIZE);
            // Viewport
            gl.viewport(vp_x, vp_y, vp_w, vp_h);
        }
    }

    /// Clean up GL resources.
    pub fn destroy(&self, gl: &glow::Context) {
        unsafe {
            gl.delete_program(self.program);
            gl.delete_program(self.torus_program);
            gl.delete_vertex_array(self.lattice_vao);
            gl.delete_buffer(self.lattice_vbo);
            gl.delete_vertex_array(self.torus_vao);
            gl.delete_buffer(self.torus_vbo);
            gl.delete_vertex_array(self.chart_vao);
            gl.delete_buffer(self.chart_vbo);
        }
    }
}

// --- Helper functions ---

fn torus_point(r_major: f32, r_minor: f32, u: f32, v: f32) -> [f32; 3] {
    [
        (r_major + r_minor * v.cos()) * u.cos(),
        (r_major + r_minor * v.cos()) * u.sin(),
        r_minor * v.sin(),
    ]
}

fn error_color(has_x: bool, has_z: bool) -> [f32; 4] {
    match (has_x, has_z) {
        (true, true) => XZ_ERR,
        (true, false) => X_ERR,
        (false, true) => Z_ERR,
        (false, false) => [GREEN[0], GREEN[1], GREEN[2], 0.3],
    }
}

fn ortho_projection(aspect: f32) -> [f32; 16] {
    let s = 1.0 / aspect.max(1.0);
    let sa = s / aspect.min(1.0) * aspect;
    [
        s, 0.0, 0.0, 0.0,
        0.0, sa, 0.0, 0.0,
        0.0, 0.0, -1.0, 0.0,
        0.0, 0.0, 0.0, 1.0,
    ]
}

fn rotation_projection(rx: f32, ry: f32, aspect: f32) -> [f32; 16] {
    let scale = 0.45;
    let sx = rx.sin();
    let cx = rx.cos();
    let sy = ry.sin();
    let cy = ry.cos();

    let a = if aspect > 1.0 { scale / aspect } else { scale };
    let b = if aspect > 1.0 { scale } else { scale * aspect };

    [
        a * cy,        0.0,     a * sy,       0.0,
        b * sx * sy,   b * cx,  -b * sx * cy, 0.0,
        -sy * cx,      sx,      cx * cy,      0.0,
        0.0,           0.0,     0.0,          1.0,
    ]
}

unsafe fn create_program(gl: &glow::Context, vert_src: &str, frag_src: &str) -> glow::Program {
    let program = gl.create_program().unwrap();

    let vs = gl.create_shader(glow::VERTEX_SHADER).unwrap();
    gl.shader_source(vs, vert_src);
    gl.compile_shader(vs);
    if !gl.get_shader_compile_status(vs) {
        panic!("Vertex shader: {}", gl.get_shader_info_log(vs));
    }

    let fs = gl.create_shader(glow::FRAGMENT_SHADER).unwrap();
    gl.shader_source(fs, frag_src);
    gl.compile_shader(fs);
    if !gl.get_shader_compile_status(fs) {
        panic!("Fragment shader: {}", gl.get_shader_info_log(fs));
    }

    gl.attach_shader(program, vs);
    gl.attach_shader(program, fs);
    gl.link_program(program);
    if !gl.get_program_link_status(program) {
        panic!("Program link: {}", gl.get_program_info_log(program));
    }

    gl.detach_shader(program, vs);
    gl.detach_shader(program, fs);
    gl.delete_shader(vs);
    gl.delete_shader(fs);

    program
}

/// Setup VAO for basic vertex format (pos + color).
unsafe fn setup_basic_vao(gl: &glow::Context, vao: glow::VertexArray, vbo: glow::Buffer) {
    gl.bind_vertex_array(Some(vao));
    gl.bind_buffer(glow::ARRAY_BUFFER, Some(vbo));

    let stride = std::mem::size_of::<Vertex>() as i32;

    gl.enable_vertex_attrib_array(0);
    gl.vertex_attrib_pointer_f32(0, 3, glow::FLOAT, false, stride, 0);

    gl.enable_vertex_attrib_array(1);
    gl.vertex_attrib_pointer_f32(1, 4, glow::FLOAT, false, stride, 12);

    gl.bind_vertex_array(None);
}

/// Setup VAO for torus vertex format (pos + color + uv + kind).
unsafe fn setup_torus_vao(gl: &glow::Context, vao: glow::VertexArray, vbo: glow::Buffer) {
    gl.bind_vertex_array(Some(vao));
    gl.bind_buffer(glow::ARRAY_BUFFER, Some(vbo));

    let stride = std::mem::size_of::<TorusVertex>() as i32;

    // location 0: pos (3 floats, offset 0)
    gl.enable_vertex_attrib_array(0);
    gl.vertex_attrib_pointer_f32(0, 3, glow::FLOAT, false, stride, 0);

    // location 1: color (4 floats, offset 12)
    gl.enable_vertex_attrib_array(1);
    gl.vertex_attrib_pointer_f32(1, 4, glow::FLOAT, false, stride, 12);

    // location 2: uv (2 floats, offset 28)
    gl.enable_vertex_attrib_array(2);
    gl.vertex_attrib_pointer_f32(2, 2, glow::FLOAT, false, stride, 28);

    // location 3: kind (1 float, offset 36)
    gl.enable_vertex_attrib_array(3);
    gl.vertex_attrib_pointer_f32(3, 1, glow::FLOAT, false, stride, 36);

    gl.bind_vertex_array(None);
}

fn upload_basic_vertices(gl: &glow::Context, vao: glow::VertexArray, vbo: glow::Buffer, verts: &[Vertex]) {
    unsafe {
        gl.bind_vertex_array(Some(vao));
        gl.bind_buffer(glow::ARRAY_BUFFER, Some(vbo));
        let data: &[u8] = std::slice::from_raw_parts(
            verts.as_ptr() as *const u8,
            verts.len() * std::mem::size_of::<Vertex>(),
        );
        gl.buffer_data_u8_slice(glow::ARRAY_BUFFER, data, glow::DYNAMIC_DRAW);
        gl.bind_vertex_array(None);
    }
}

fn upload_torus_vertices(gl: &glow::Context, vao: glow::VertexArray, vbo: glow::Buffer, verts: &[TorusVertex]) {
    unsafe {
        gl.bind_vertex_array(Some(vao));
        gl.bind_buffer(glow::ARRAY_BUFFER, Some(vbo));
        let data: &[u8] = std::slice::from_raw_parts(
            verts.as_ptr() as *const u8,
            verts.len() * std::mem::size_of::<TorusVertex>(),
        );
        gl.buffer_data_u8_slice(glow::ARRAY_BUFFER, data, glow::DYNAMIC_DRAW);
        gl.bind_vertex_array(None);
    }
}

unsafe fn set_uniform_mat4(gl: &glow::Context, program: glow::Program, name: &str, mat: &[f32; 16]) {
    let loc = gl.get_uniform_location(program, name);
    if let Some(loc) = loc {
        gl.uniform_matrix_4_f32_slice(Some(&loc), false, mat);
    }
}

unsafe fn set_uniform_f32(gl: &glow::Context, program: glow::Program, name: &str, val: f32) {
    let loc = gl.get_uniform_location(program, name);
    if let Some(loc) = loc {
        gl.uniform_1_f32(Some(&loc), val);
    }
}
