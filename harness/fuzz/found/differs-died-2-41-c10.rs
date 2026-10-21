// Found by fuzz.py: seed 2-41, case c10, edition 2024, backend llvm.
// differs: died
// Reduced in 150 builds. Again: fuzz.py check differs-died-2-41-c10.rs
// rustd's program ended with status -11 in this case
// 
mod c10 {
    use super::*;
    #[derive(Clone, Debug, PartialEq, PartialOrd, Copy, Eq, Ord, Hash)]
    pub struct S1(pub Option<i128>, pub Option<i128>, pub char);
    impl Mix for S1 {
        fn mix(&self) {
        }
    }
    #[derive(Clone, Debug, PartialEq, PartialOrd, Copy, Eq, Ord, Hash)]
    #[repr(u8)]
    pub enum E2 {
        V0,
        V1,
        V2,
        V3,
        V4,
    }
    #[derive(Clone, Debug, PartialEq, PartialOrd, Copy)]
    #[repr(C)]
    pub struct S3(pub f64);
    impl Mix for S3 {
        fn mix(&self) {
        }
    }
    #[derive(Clone, Debug, PartialEq, PartialOrd)]
    pub struct S4 { pub f0: i128, pub f1: S3, pub f2: Option<i128> }
    #[inline]
    pub fn f28<G26: Mix + Clone + Debug + PartialOrd, G27: Mix + Clone + Debug + PartialOrd>(a29: G26, a30: G27, a31: &S1) -> G27 {
        let mut v32: i128 = (if (48542219327495855984974382813297228600u128.is_power_of_two()) { ((-13170945966552493715529789122052601102i128) >> (262143u32 % 128)) } else { (100i128 >> (40u32 % 128)) });
        ({ let t33: i8 = (-10i8); a30.clone() })
    }
    pub fn run() {
        let S4 { f0: p114, f1: S3(_), f2: p115 }: S4 = twice::<S4>(&S4 { f0: (-69720137821400948044068661629433897936i128), f1: S3(7.0f64), f2: Some((-75821193675147744973527649488901269754i128)) }).1;
        let mut v182: i128 = ((unsafe { std::mem::transmute::<u64, u64>(16228910211317703321u64) } as i128) << ((E2::V2 as u32) % 128));
        let mut v183: i128 = 12i128;
                'l209: for i208 in ((14i8..20i8).rev()) {
                    if (f28::<(NonZeroU8, Vec<u128>, [u128; 5]), bool>((if (false) { (NonZeroU8::new(255u8).unwrap(), vec![7u128], [18u128; 5]) } else { (NonZeroU8::new(155u8).unwrap(), Vec::<u128>::new(), [191163164466629563746542610771349467710u128; 5]) }), Some(Some(Box::new(273320163283813499618987362033968314131u128))).is_some(), &f28::<[String; 1], S1>([String::from("ff")], S1(Some((-11i128)), Some(2147483648i128), 'a'), &S1(Some(32i128), Some((-14i128)), '\u{e000}')))) { continue 'l209; }
                }
                if let Some(p229) = (Some(f64::MAX).map(|x228: f64| -> Box<u128> { Box::new(2u128) })) {
                    let v230: i128 = f28::<S3, i128>(S3(Ok::<f64, Option<[char; 2]>>(4294967296.0f64).unwrap_or(1e30f64)), (E2::V1 as i128).checked_mul(85070591730234615865843651857942052863i128).unwrap_or(larger::<i128>(v183, v182)), &S1(p115, Some(Some(170141183460469231731687303715884105727i128)).map_or(p115, |x233: Option<i128>| -> Option<i128> { p115 }), String::from("😀").chars().next().unwrap_or('\u{10FFFF}')));
                }
    }
}
