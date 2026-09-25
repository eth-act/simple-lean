/// Floor average of two `u64`s without overflow.
///
/// `a + b = 2·(a & b) + (a ^ b)`, so `(a + b) / 2 = (a & b) + (a ^ b) / 2`,
/// and neither term can overflow. Proved equal to `Avg.avgSpec` in
/// `Avg/Proofs/Avg.lean`.
pub fn avg(a: u64, b: u64) -> u64 {
    (a & b) + ((a ^ b) >> 1)
}

#[cfg(test)]
mod tests {
    use super::avg;

    #[test]
    fn extremes() {
        assert_eq!(avg(u64::MAX, u64::MAX), u64::MAX);
        assert_eq!(avg(u64::MAX, u64::MAX - 1), u64::MAX - 1);
        assert_eq!(avg(0, u64::MAX), u64::MAX / 2);
    }
}
