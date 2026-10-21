//! Salsa's generic methods call tracing wrappers through module reexports. The static
//! lookup could not count items in a macro reached through an ordinary module import.

pub fn run() -> ((u32, u32, u32), (u32, u32, u32), (u32, u32, u32)) {
    let site = foreign::Callsite(|| 0u8);
    (site.visit(), foreign::visit_callsites(), site.visit())
}
