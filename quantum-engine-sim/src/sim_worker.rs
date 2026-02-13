//! Background simulation worker thread.
//!
//! Runs heavy computations off the main thread so the GUI never blocks.

use crossbeam_channel::{Receiver, Sender};
use std::thread;

use crate::cnt_bridge;
use crate::cnt_physics;
use crate::covariant::{self, ContinuumLoss, DescentResult, Method, TorusPoint};
use crate::engine::{self, EngineConfig, EngineResult};
use crate::torus::TorusLattice;
use crate::vacuum;

/// Request sent from GUI to worker.
pub enum SimRequest {
    /// Run full engine simulation with given config.
    RunEngine { config: EngineConfig },
    /// Run covariant descent comparison (Euclidean vs Covariant).
    RunDescent {
        n: usize,
        eta: f64,
        start: TorusPoint,
        target: TorusPoint,
    },
    /// Run scaling study across multiple lattice sizes.
    RunScaling {
        config: EngineConfig,
        sizes: Vec<usize>,
    },
    /// Run convergence validation across lattice sizes.
    RunConvergence {
        sizes: Vec<usize>,
        eta: f64,
    },
    /// Run CNT Doppler physics evaluation + toric code MC.
    RunCntEval {
        params: cnt_physics::PhysicsParams,
        lattice_n: usize,
        gate_time_ns: f64,
        mc_trials: usize,
    },
    /// Run CNT threshold sweep for chart data.
    RunCntSweep {
        lattice_n: usize,
        mc_trials: usize,
        operating_p: f64,
    },
}

/// Scaling study entry for one lattice size.
#[derive(Debug, Clone)]
pub struct ScalingEntry {
    pub n: usize,
    pub spectral_gap: f64,
    pub dce_pair_rate: f64,
    pub efficiency: f64,
    pub efficiency_bare: f64,
    pub coherence_enhancement: f64,
}

/// Response sent from worker to GUI.
pub enum SimResponse {
    Engine(EngineResult),
    Descent {
        euclidean: DescentResult,
        covariant: DescentResult,
    },
    Scaling(Vec<ScalingEntry>),
    Convergence(Vec<(usize, f64, f64)>),
    /// CNT physics + MC result for current parameters.
    CntEvaluated {
        physics: cnt_physics::PhysicsResult,
        p_error: f64,
        mc_result: toric_code_sim::prelude::SimResult,
        snapshot: cnt_bridge::LatticeSnapshot,
    },
    /// CNT threshold sweep chart data.
    CntSweptChart(cnt_bridge::ChartData),
}

/// Handle to communicate with the background worker.
pub struct SimWorker {
    pub tx: Sender<SimRequest>,
    pub rx: Receiver<SimResponse>,
}

impl SimWorker {
    /// Spawn the background worker thread.
    pub fn spawn() -> Self {
        let (req_tx, req_rx) = crossbeam_channel::unbounded::<SimRequest>();
        let (resp_tx, resp_rx) = crossbeam_channel::unbounded::<SimResponse>();

        thread::spawn(move || {
            while let Ok(req) = req_rx.recv() {
                match req {
                    SimRequest::RunEngine { config } => {
                        let result = engine::simulate(&config);
                        let _ = resp_tx.send(SimResponse::Engine(result));
                    }
                    SimRequest::RunDescent {
                        n,
                        eta,
                        start,
                        target,
                    } => {
                        let loss = ContinuumLoss::new(target, 3);
                        let euclidean = covariant::descent(
                            &loss,
                            start,
                            Method::Euclidean,
                            eta,
                            2000,
                            0.01,
                            n,
                        );
                        let covariant = covariant::descent(
                            &loss,
                            start,
                            Method::Covariant,
                            eta,
                            2000,
                            0.01,
                            n,
                        );
                        let _ = resp_tx.send(SimResponse::Descent {
                            euclidean,
                            covariant,
                        });
                    }
                    SimRequest::RunScaling { config, sizes } => {
                        let results = engine::scaling_study(&config, &sizes);
                        let entries: Vec<ScalingEntry> = results
                            .iter()
                            .map(|r| {
                                let t =
                                    TorusLattice::new(r.config.n, r.config.l_min);
                                let d = vacuum::dynamical_casimir(
                                    &t,
                                    r.config.modulation_depth,
                                    r.drive_freq,
                                );
                                ScalingEntry {
                                    n: r.config.n,
                                    spectral_gap: r.cycle.spectral_gap,
                                    dce_pair_rate: d.pair_rate,
                                    efficiency: r.cycle.efficiency,
                                    efficiency_bare: r.efficiency_unprotected,
                                    coherence_enhancement: r.coherence_enhancement,
                                }
                            })
                            .collect();
                        let _ = resp_tx.send(SimResponse::Scaling(entries));
                    }
                    SimRequest::RunConvergence { sizes, eta } => {
                        let results = covariant::convergence_validation(&sizes, eta);
                        let _ = resp_tx.send(SimResponse::Convergence(results));
                    }
                    SimRequest::RunCntEval {
                        params,
                        lattice_n,
                        gate_time_ns,
                        mc_trials,
                    } => {
                        let physics = cnt_physics::evaluate(&params);
                        let p_error = cnt_bridge::t2_to_p(physics.t2_ns, gate_time_ns);
                        let mc_result = cnt_bridge::run_mc(lattice_n, p_error, mc_trials);
                        let snapshot = cnt_bridge::capture_snapshot(lattice_n, p_error);
                        let _ = resp_tx.send(SimResponse::CntEvaluated {
                            physics,
                            p_error,
                            mc_result,
                            snapshot,
                        });
                    }
                    SimRequest::RunCntSweep {
                        lattice_n,
                        mc_trials,
                        operating_p,
                    } => {
                        let mut chart =
                            cnt_bridge::quick_sweep(lattice_n, operating_p, mc_trials);
                        chart.operating_p = operating_p;
                        let _ = resp_tx.send(SimResponse::CntSweptChart(chart));
                    }
                }
            }
        });

        SimWorker {
            tx: req_tx,
            rx: resp_rx,
        }
    }

    /// Send a request (non-blocking).
    pub fn send(&self, req: SimRequest) {
        let _ = self.tx.send(req);
    }

    /// Try to receive a response (non-blocking).
    pub fn try_recv(&self) -> Option<SimResponse> {
        self.rx.try_recv().ok()
    }
}
