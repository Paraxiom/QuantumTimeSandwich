//! Background simulation worker thread.
//!
//! Runs MC simulations off the main thread so the GUI never blocks.

use crossbeam_channel::{Receiver, Sender};
use std::thread;

use crate::bridge::{self, ChartData, LatticeSnapshot};
use toric_code_sim::prelude::SimResult;
use crate::physics::{self, PhysicsParams, PhysicsResult};

/// Request sent from GUI to worker.
#[derive(Debug, Clone)]
pub enum SimRequest {
    /// Compute physics + single MC trial + snapshot.
    Evaluate {
        params: PhysicsParams,
        lattice_n: usize,
        gate_time_ns: f64,
        mc_trials: usize,
    },
    /// Run a threshold sweep for chart data.
    Sweep {
        lattice_n: usize,
        mc_trials: usize,
        operating_p: f64,
    },
}

/// Response sent from worker to GUI.
#[derive(Debug, Clone)]
pub enum SimResponse {
    /// Physics + MC result for current parameters.
    Evaluated {
        physics: PhysicsResult,
        p_error: f64,
        mc_result: SimResult,
        snapshot: LatticeSnapshot,
    },
    /// Threshold sweep chart data.
    SweptChart(ChartData),
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
                    SimRequest::Evaluate {
                        params,
                        lattice_n,
                        gate_time_ns,
                        mc_trials,
                    } => {
                        let physics = physics::evaluate(&params);
                        let p_error = bridge::t2_to_p(physics.t2_ns, gate_time_ns);
                        let mc_result = bridge::run_mc(lattice_n, p_error, mc_trials);
                        let snapshot = bridge::capture_snapshot(lattice_n, p_error);

                        let _ = resp_tx.send(SimResponse::Evaluated {
                            physics,
                            p_error,
                            mc_result,
                            snapshot,
                        });
                    }
                    SimRequest::Sweep {
                        lattice_n,
                        mc_trials,
                        operating_p,
                    } => {
                        let mut chart =
                            bridge::quick_sweep(lattice_n, operating_p, mc_trials);
                        chart.operating_p = operating_p;
                        let _ = resp_tx.send(SimResponse::SweptChart(chart));
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
