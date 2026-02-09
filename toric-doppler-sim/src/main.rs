//! Combined Doppler-cooling → toric-code simulation with native egui visualization.

mod physics;
mod bridge;
mod worker;
mod gui;

fn main() -> eframe::Result<()> {
    let options = eframe::NativeOptions {
        viewport: eframe::egui::ViewportBuilder::default()
            .with_inner_size([1200.0, 800.0])
            .with_title("Doppler Cooling → Toric Code  ·  Paraxiom"),
        renderer: eframe::Renderer::Wgpu,
        ..Default::default()
    };

    eframe::run_native(
        "toric-doppler-sim",
        options,
        Box::new(|cc| Ok(Box::new(gui::ToricDopplerApp::new(cc)))),
    )
}
