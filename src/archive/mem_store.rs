use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::*;

/// An ArchiveStore implementation that keeps objects in memory.
/// Mainly intended for testing purposes.
pub struct MemStore {
    pub objects: Rc<RefCell<HashMap<String, Vec<u8>>>>,
    finished_puts: Vec<(String, Result<()>)>,
    finished_gets: Vec<(String, Result<Vec<u8>>)>,
    ack_puts: bool,
    ack_gets: bool,
}

impl Default for MemStore {
    fn default() -> Self {
        Self::new()
    }
}

impl MemStore {
    pub fn new() -> Self {
        MemStore {
            objects: Rc::new(RefCell::new(HashMap::new())),
            finished_puts: Vec::new(),
            finished_gets: Vec::new(),
            ack_puts: true,
            ack_gets: true,
        }
    }

    pub fn new_with_objects(objects: Rc<RefCell<HashMap<String, Vec<u8>>>>) -> Self {
        MemStore {
            objects,
            finished_puts: Vec::new(),
            finished_gets: Vec::new(),
            ack_puts: true,
            ack_gets: true,
        }
    }

    fn try_put_object(&mut self, name: &str, data: Vec<u8>) -> Result<()> {
        self.objects.borrow_mut().insert(name.to_string(), data);
        Ok(())
    }

    fn try_get_object(&self, name: &str) -> Result<Vec<u8>> {
        self.objects.borrow().get(name).cloned().ok_or_else(|| {
            crate::ubiblk_error!(ArchiveError {
                description: format!("Object {} not found", name),
            })
        })
    }

    #[cfg(test)]
    pub fn list_objects(&self) -> Result<Vec<String>> {
        Ok(self.objects.borrow().keys().cloned().collect())
    }
}

impl ArchiveStore for MemStore {
    fn start_put_object(&mut self, name: &str, data: Vec<u8>) {
        let result = self.try_put_object(name, data);
        if self.ack_puts {
            self.finished_puts.push((name.to_string(), result));
        }
    }

    fn start_get_object(&mut self, name: &str) {
        let result = self.try_get_object(name);
        if self.ack_gets {
            self.finished_gets.push((name.to_string(), result));
        }
    }

    fn poll_puts(&mut self) -> Vec<(String, Result<()>)> {
        std::mem::take(&mut self.finished_puts)
    }

    fn poll_gets(&mut self) -> Vec<(String, Result<Vec<u8>>)> {
        std::mem::take(&mut self.finished_gets)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_put_timeout() {
        let mut store = MemStore::new();
        store.ack_puts = false; // Disable immediate acknowledgment

        let result = store.put_object("test_object", b"data", Duration::from_millis(10));
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err
            .to_string()
            .contains("Timeout while putting object test_object"));
    }

    #[test]
    fn test_get_timeout() {
        let mut store = MemStore::new();
        store.ack_gets = false; // Disable immediate acknowledgment

        let result = store.get_object("non_existent_object", Duration::from_millis(10));
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err
            .to_string()
            .contains("Timeout while getting object non_existent_object"));
    }
}
