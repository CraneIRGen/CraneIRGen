/// An uninhabited type.
///
/// Useful for modeling Wasm's bottom types or `cf-constructor`'d off features.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Uninhabited {}
