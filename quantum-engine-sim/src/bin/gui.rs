fn main() -> eframe::Result<()> {
    let options = eframe::NativeOptions {
        viewport: eframe::egui::ViewportBuilder::default()
            .with_inner_size([1400.0, 900.0])
            .with_title("Quantum Engine \u{00b7} Paraxiom"),
        renderer: eframe::Renderer::Wgpu,
        ..Default::default()
    };

    eframe::run_native(
        "quantum-engine-sim",
        options,
        Box::new(|cc| Ok(Box::new(quantum_engine_sim::gui::QuantumEngineApp::new(cc)))),
    )
}
