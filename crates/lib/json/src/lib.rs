//! JSON serialization used by Nucleus.

pub use serde_json;
pub use serde_json::*;

#[cfg(test)]
mod tests {
    #[test]
    fn json_macro_round_trips() {
        let value = crate::json!({ "answer": 42 });
        let rendered = crate::to_string(&value).unwrap();

        assert_eq!(rendered, r#"{"answer":42}"#);
        assert_eq!(crate::from_str::<crate::Value>(&rendered).unwrap(), value);
    }
}
