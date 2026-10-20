// Found by fuzz.py: seed 2-0, case c22, edition 2021, backend llvm.
// differs: checksum
// Reduced in 85 builds. Again: fuzz.py check differs-checksum-2-0-c22.rs
// rustc:
// c22 a24e7a9ae3a12ecf ok
// rustd:
// c22 e0115aa04130bb23 ok
mod c22 {
    use super::*;
    pub fn run() {
            #[inline(never)] fn spread(a: u8, b: i128, c: u64, d: i128, e: u32, f: i128, g: i128) -> (i128, u8, i128) { (b.wrapping_add(d) ^ f, a.wrapping_add(c as u8).wrapping_add(e as u8), g.wrapping_sub(b)) }
            #[inline(never)] extern "C" fn c_side(a: i128, b: u8, c: i128) -> i128 { a.wrapping_mul(3).wrapping_add(c) ^ b as i128 }
            #[inline(never)] fn by_ref(a: &i128, b: &mut i128) -> i128 { *b = b.wrapping_add(*a); *a ^ *b }
            #[derive(Clone, Copy)] struct Wide { tag: u8, value: i128, pair: [i128; 2] }
            #[inline(never)] fn pass(w: Wide, extra: Option<i128>) -> Wide { Wide { tag: w.tag.wrapping_add(1), value: w.pair[1] ^ extra.unwrap_or(1), pair: [w.value, w.pair[0]] } }
            let (a, b): (i128, i128) = (black_box((((1u128 << 127)) as u128 as i128).wrapping_neg()), black_box(((340282366920938463463374607431768211297) as u128 as i128)));
            let got = spread(1, a, 2, b, 3, a ^ b, !a); got.0.mix(); got.1.mix(); got.2.mix();
        'l270: for x269 in ((unsafe { let mut slot = MaybeUninit::<Option<Box<String>>>::uninit(); slot.write(None::<Box<String>>); slot.assume_init() }).into_iter()) {
                { let mut counts: Box<dyn Iterator<Item = u64>> = Box::new((1..4u64).map(|it| it * 3)); feed(counts.next().unwrap_or(0)); feed(counts.sum()); }
        }
    }
}
