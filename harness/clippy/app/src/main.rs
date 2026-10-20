use util::Stack;

fn report(stack: &Stack) {
    println!("{} {:?}", stack.len(), stack.top());
}

fn empty(items: &[u8], text: &str) -> (bool, bool, bool) {
    let a = items.len() == 0;
    let b = text.len() != 0;
    let c = items.len() > 0;
    (a, b, c)
}

fn pick(flag: bool) -> bool {
    if flag { true } else { false }
}

fn flip(flag: bool) -> bool {
    if flag {
        false
    } else {
        true
    }
}

fn nothing() {}

fn main() {
    let mut stack = Stack::new();
    stack.push(3);
    let unit = nothing();
    println!("{unit:?}");
    report(&stack);
    let mut x = 5;
    x = x;
    println!("{:?} {} {}", empty(&[1], "a"), pick(true), flip(false));
    println!("{}", util::scaled(x) + 0);
    println!("{} {}", util::checked(true), util::through_macro(false));
    let k = 3u32;
    println!("{}", k == k);
    println!("{}", util::allowed(1));
}
