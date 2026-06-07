//! Reference-free restoration benchmark for the soroban-ret decompiler.
//!
//! Given a corpus of Soroban contract WASM binaries (no original source), this
//! crate measures how completely the decompiler reconstructs each contract and
//! where it falls short, emitting a JSON report, a self-contained HTML
//! dashboard, and a Markdown summary, with optional diffing against a committed
//! baseline.
//!
//! See [`metrics`] for the scoring definition.

pub mod diff;
pub mod markdown;
pub mod metrics;
pub mod report_html;
