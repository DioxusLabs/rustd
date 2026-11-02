pub(crate) fn capacity() -> Option<u16> {
    let value = std::env::var_os("RUSTD_LRU")?;
    let capacity = value.to_str().and_then(parse);
    if capacity.is_none() {
        eprintln!("invalid RUSTD_LRU: expected off or an integer from 0 to 65535; using defaults");
    }
    capacity
}

fn parse(value: &str) -> Option<u16> {
    if value == "off" { Some(0) } else { value.parse().ok() }
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
