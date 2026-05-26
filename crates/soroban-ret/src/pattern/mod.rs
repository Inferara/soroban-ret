/// Pattern matching module.
///
/// Lifts WASM instructions into Soroban-aware IR by recognizing
/// host function call patterns, dispatch wrappers, and type conversions.
pub mod dispatch;
pub mod host_calls;
pub mod lifter;
pub mod structurize;

pub use lifter::lift_functions;
