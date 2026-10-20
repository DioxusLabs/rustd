pub struct Stack {
    items: Vec<u32>,
}

impl Stack {
    pub fn new() -> Stack {
        Stack { items: Vec::new() }
    }

    pub fn push(&mut self, item: u32) {
        self.items.push(item);
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    // Clippy leaves `len() == 0` alone inside `is_empty` itself.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn top(&self) -> Option<u32> {
        return self.items.last().copied();
    }
}

impl Default for Stack {
    fn default() -> Stack {
        Stack::new()
    }
}

pub fn scaled(x: u64) -> u64 {
    x * 1 + 0
}

#[allow(clippy::needless_return)]
pub fn allowed(x: u64) -> u64 {
    return x + 1;
}

pub fn checked(flag: bool) -> bool {
    if flag == true {
        return false;
    }
    flag != false
}

macro_rules! same {
    ($x:expr) => {
        $x == true
    };
}

pub fn through_macro(flag: bool) -> bool {
    same!(flag)
}
