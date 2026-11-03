/// The capacity and the queries it is for. The durability ladder keeps syntax unbounded by
/// default: its first MEDIUM change verifies every memo above syntax, and an evicted value
/// re-executes them all.
pub(crate) fn settings() -> (Option<u16>, Option<Scope>) {
    let Some(value) = std::env::var_os("RUSTD_LRU") else {
        return if crate::tree::ladder() { (Some(0), Some(Scope::Syntax)) } else { (None, None) };
    };
    let capacity = value.to_str().and_then(parse);
    if capacity.is_none() {
        eprintln!("invalid RUSTD_LRU: expected off or an integer from 0 to 65535; using defaults");
    }
    (capacity, scope())
}

fn parse(value: &str) -> Option<u16> {
    if value == "off" { Some(0) } else { value.parse().ok() }
}

/// `RUSTD_LRU_SCOPE=syntax|semantic` limits `RUSTD_LRU` to one group of queries; the other
/// group keeps its defaults.
fn scope() -> Option<Scope> {
    match std::env::var("RUSTD_LRU_SCOPE").ok()?.as_str() {
        "syntax" => Some(Scope::Syntax),
        "semantic" => Some(Scope::Semantic),
        other => {
            eprintln!("invalid RUSTD_LRU_SCOPE {other:?}: expected syntax or semantic; ignored");
            None
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Scope {
    Syntax,
    Semantic,
}

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn capacities() {
        assert_eq!(parse("off"), Some(0));
        assert_eq!(parse("0"), Some(0));
        assert_eq!(parse("8192"), Some(8192));
        assert_eq!(parse("65535"), Some(65535));
    }

    #[test]
    fn invalid_capacities_use_defaults() {
        for value in ["", "default", "-1", "65536", " 512", "OFF"] {
            assert_eq!(parse(value), None, "{value}");
        }
    }
}
