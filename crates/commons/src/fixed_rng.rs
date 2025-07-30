use lazy_static::lazy_static;
use rand::Rng;
use std::cell::RefCell;
use std::sync::Mutex;

lazy_static! {
    static ref GLOBAL_RNG: Mutex<Option<FixedRng>> = Mutex::new(None);
}

pub struct FixedRng {
    sequence: RefCell<Vec<u32>>,
}

impl FixedRng {
    pub fn new() -> FixedRng {
        FixedRng {
            sequence: RefCell::new(vec![
                2, 3, 1, 4, 3, 0, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
                4, 4, 4,
            ]),
        }
    }

    pub fn gen_range(&self, _range: std::ops::Range<u32>) -> u32 {
        self.sequence.borrow_mut().remove(0)
    }
}

pub fn initialize_rng() {
    let mut rng = GLOBAL_RNG.lock().unwrap();
    *rng = Some(FixedRng::new());
}

pub fn gen_and_print_range(start: u32, end: u32, is_instrs: bool) -> u32 {
    let mut rng_guard = GLOBAL_RNG.lock().unwrap();
    if let Some(rng) = rng_guard.as_mut() {
        let mut random_number = 0;
        if is_instrs {
            random_number = 4;
        } else {
            random_number = rand::thread_rng().gen_range(start..end);
        }

        random_number
    } else {
        panic!("The RNG has not been initialized");
    }
}
