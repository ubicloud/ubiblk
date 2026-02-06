use std::cell::RefCell;
use std::fs::{File, OpenOptions};
use std::io::Write;

thread_local! {
    static TRACE_FILE: RefCell<Option<File>> = const { RefCell::new(None) };
}

/// Initialize TLA+ trace logging to the given file path.
/// Call this once at startup (or once per test thread) before any trace events are emitted.
pub fn init(path: &str) {
    let file = OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(path)
        .expect("failed to open TLA+ trace file");
    TRACE_FILE.with(|f| {
        *f.borrow_mut() = Some(file);
    });
}

/// Log a TLA+ action as an NDJSON line.
/// `action` is the TLA+ action name, `fields` is a JSON object with variables.
pub fn log_action(action: &str, fields: serde_json::Value) {
    TRACE_FILE.with(|f| {
        let mut guard = f.borrow_mut();
        if let Some(file) = guard.as_mut() {
            let mut obj = fields;
            if let serde_json::Value::Object(ref mut map) = obj {
                map.insert(
                    "action".to_string(),
                    serde_json::Value::String(action.to_string()),
                );
            }
            let _ = writeln!(file, "{}", obj);
        }
    });
}
