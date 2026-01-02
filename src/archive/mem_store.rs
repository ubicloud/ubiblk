use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::*;

#[derive(Clone)]
pub struct MemStore {
    objects: Rc<RefCell<HashMap<String, Vec<u8>>>>,
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
        }
    }
}

impl ArchiveStore for MemStore {
    fn put_object(&mut self, name: &str, data: &[u8]) -> Result<()> {
        self.objects
            .borrow_mut()
            .insert(name.to_string(), data.to_vec());
        Ok(())
    }

    fn get_object(&self, name: &str) -> Result<Vec<u8>> {
        self.objects
            .borrow()
            .get(name)
            .cloned()
            .ok_or_else(|| crate::UbiblkError::ArchiveError {
                description: format!("Object {} not found", name),
            })
    }

    fn list_objects(&self) -> Result<Vec<String>> {
        Ok(self.objects.borrow().keys().cloned().collect())
    }
}
