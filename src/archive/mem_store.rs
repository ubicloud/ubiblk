use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::*;

pub struct MemStore {
    pub objects: Rc<RefCell<HashMap<String, Vec<u8>>>>,
    finished_puts: Vec<(String, Result<()>)>,
    finished_gets: Vec<(String, Result<Vec<u8>>)>,
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
        }
    }

    pub fn new_with_objects(objects: Rc<RefCell<HashMap<String, Vec<u8>>>>) -> Self {
        MemStore {
            objects,
            finished_puts: Vec::new(),
            finished_gets: Vec::new(),
        }
    }

    fn try_put_object(&mut self, name: &str, data: &[u8]) -> Result<()> {
        self.objects
            .borrow_mut()
            .insert(name.to_string(), data.to_vec());
        Ok(())
    }

    fn try_get_object(&self, name: &str) -> Result<Vec<u8>> {
        self.objects.borrow().get(name).cloned().ok_or_else(|| {
            crate::ubiblk_error!(ArchiveError {
                description: format!("Object {} not found", name),
            })
        })
    }
}

impl ArchiveStore for MemStore {
    fn start_put_object(&mut self, name: &str, data: &[u8]) {
        let result = self.try_put_object(name, data);
        self.finished_puts.push((name.to_string(), result));
    }

    fn start_get_object(&mut self, name: &str) {
        let result = self.try_get_object(name);
        self.finished_gets.push((name.to_string(), result));
    }

    fn poll_puts(&mut self) -> Vec<(String, Result<()>)> {
        std::mem::take(&mut self.finished_puts)
    }

    fn poll_gets(&mut self) -> Vec<(String, Result<Vec<u8>>)> {
        std::mem::take(&mut self.finished_gets)
    }

    fn list_objects(&self) -> Result<Vec<String>> {
        Ok(self.objects.borrow().keys().cloned().collect())
    }
}
