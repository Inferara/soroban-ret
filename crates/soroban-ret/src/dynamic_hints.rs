//! Runtime-free hints that can guide conservative decompiler repairs.
//!
//! These types intentionally live in the core crate and avoid any dependency on
//! Wasmtime or runtime inspection crates. Producers can translate runtime data
//! into this small value model before calling the core decompiler.

/// Optional hints for a decompilation run.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct DecompileHints {
    /// Function-scoped hints keyed by decompiled contract function name.
    pub functions: Vec<FunctionHints>,
}

impl DecompileHints {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_functions(functions: Vec<FunctionHints>) -> Self {
        Self { functions }
    }

    pub fn is_empty(&self) -> bool {
        self.functions.iter().all(FunctionHints::is_empty)
    }

    pub fn push_function(&mut self, function_hints: FunctionHints) {
        if !function_hints.is_empty() {
            self.functions.push(function_hints);
        }
    }
}

/// Hints that apply to one contract function.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct FunctionHints {
    /// Decompiled contract function name.
    pub function_name: String,
    /// Storage observations associated with this function.
    pub storage: Vec<StorageHint>,
    /// Event observations associated with this function.
    pub events: Vec<EventHint>,
    /// Authorization observations associated with this function.
    pub auth: Vec<AuthHint>,
    /// Cross-contract invocation observations associated with this function.
    pub invokes: Vec<InvokeHint>,
}

impl FunctionHints {
    pub fn new(function_name: impl Into<String>) -> Self {
        Self {
            function_name: function_name.into(),
            storage: Vec::new(),
            events: Vec::new(),
            auth: Vec::new(),
            invokes: Vec::new(),
        }
    }

    pub fn with_storage<I, S>(function_name: impl Into<String>, storage: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<StorageHint>,
    {
        let mut hints = Self::new(function_name);
        for storage_hint in storage {
            hints.push_storage(storage_hint);
        }
        hints
    }

    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
            && self.events.is_empty()
            && self.auth.is_empty()
            && self.invokes.is_empty()
    }

    pub fn push_storage(&mut self, storage_hint: impl Into<StorageHint>) {
        let storage_hint = storage_hint.into();
        if !self.storage.contains(&storage_hint) {
            self.storage.push(storage_hint);
        }
    }

    pub fn push_event(&mut self, event_hint: impl Into<EventHint>) {
        let event_hint = event_hint.into();
        if !self.events.contains(&event_hint) {
            self.events.push(event_hint);
        }
    }

    pub fn push_auth(&mut self, auth_hint: impl Into<AuthHint>) {
        let auth_hint = auth_hint.into();
        if !self.auth.contains(&auth_hint) {
            self.auth.push(auth_hint);
        }
    }

    pub fn push_invoke(&mut self, invoke_hint: impl Into<InvokeHint>) {
        let invoke_hint = invoke_hint.into();
        if !self.invokes.contains(&invoke_hint) {
            self.invokes.push(invoke_hint);
        }
    }
}

/// A storage-related observation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct StorageHint {
    /// Observed storage key value.
    pub key: HintValue,
}

impl StorageHint {
    pub fn new(key: HintValue) -> Self {
        Self { key }
    }
}

impl From<HintValue> for StorageHint {
    fn from(key: HintValue) -> Self {
        Self::new(key)
    }
}

/// Event-related observation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct EventHint {
    /// Observed event topics.
    pub topics: Vec<HintValue>,
    /// Observed event data.
    pub data: Vec<HintValue>,
}

impl EventHint {
    pub fn new(topics: Vec<HintValue>, data: Vec<HintValue>) -> Self {
        Self { topics, data }
    }
}

/// Authorization-related observation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct AuthHint {
    /// Observed address when it can be represented without runtime handles.
    pub address: Option<HintValue>,
    /// Observed auth arguments.
    pub args: Vec<HintValue>,
}

impl AuthHint {
    pub fn new(address: Option<HintValue>, args: Vec<HintValue>) -> Self {
        Self { address, args }
    }
}

/// Cross-contract invocation observation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct InvokeHint {
    /// Observed function name when it can be represented without runtime handles.
    pub function: Option<HintValue>,
    /// Observed invocation arguments.
    pub args: Vec<HintValue>,
}

impl InvokeHint {
    pub fn new(function: Option<HintValue>, args: Vec<HintValue>) -> Self {
        Self { function, args }
    }
}

/// Runtime-independent values that hint producers may attach to core hints.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum HintValue {
    Bool(bool),
    U32(u32),
    I32(i32),
    U64(u64),
    I64(i64),
    Symbol(String),
    Void,
    U128(u128),
    I128(i128),
    String(String),
    Bytes(Vec<u8>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn function_hints_with_storage_uses_constructors_and_dedupes_storage() {
        let hints = FunctionHints::with_storage(
            "read",
            [
                StorageHint::new(HintValue::Symbol("Balance".to_string())),
                StorageHint::new(HintValue::Symbol("Balance".to_string())),
                StorageHint::new(HintValue::String("account".to_string())),
            ],
        );

        assert_eq!(hints.function_name, "read");
        assert!(hints.events.is_empty());
        assert!(hints.auth.is_empty());
        assert!(hints.invokes.is_empty());
        assert_eq!(
            hints.storage,
            vec![
                StorageHint::new(HintValue::Symbol("Balance".to_string())),
                StorageHint::new(HintValue::String("account".to_string())),
            ]
        );
    }

    #[test]
    fn decompile_hints_helpers_skip_empty_functions() {
        let mut hints = DecompileHints::new();
        assert!(hints.is_empty());

        hints.push_function(FunctionHints::new("read"));
        assert!(hints.is_empty());

        let mut function_hints = FunctionHints::new("read");
        function_hints.push_storage(HintValue::U32(7));
        hints.push_function(function_hints);

        assert!(!hints.is_empty());
        assert_eq!(hints.functions.len(), 1);
    }

    #[test]
    fn function_hints_dedupes_event_auth_and_invoke_hints() {
        let mut hints = FunctionHints::new("transfer");

        let event = EventHint::new(
            vec![HintValue::Symbol("transfer".to_string())],
            vec![HintValue::U64(10)],
        );
        hints.push_event(event.clone());
        hints.push_event(event.clone());
        hints.push_event(EventHint::new(Vec::new(), vec![HintValue::Bool(true)]));

        let auth = AuthHint::new(Some(HintValue::Symbol("admin".to_string())), Vec::new());
        hints.push_auth(auth.clone());
        hints.push_auth(auth.clone());

        let invoke = InvokeHint::new(
            Some(HintValue::Symbol("approve".to_string())),
            vec![HintValue::U32(1)],
        );
        hints.push_invoke(invoke.clone());
        hints.push_invoke(invoke.clone());

        assert_eq!(
            hints.events,
            vec![
                event,
                EventHint::new(Vec::new(), vec![HintValue::Bool(true)])
            ]
        );
        assert_eq!(hints.auth, vec![auth]);
        assert_eq!(hints.invokes, vec![invoke]);
    }
}
