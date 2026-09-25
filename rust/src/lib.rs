#![cfg_attr(not(test), no_std)]

/// Floor average of two `u64`s without overflow.
///
/// `a + b = 2·(a & b) + (a ^ b)`, so `(a + b) / 2 = (a & b) + (a ^ b) / 2`,
/// and neither term can overflow. Proved to satisfy the spec `Avg.IsAvg` in
/// `aeneas/AvgAeneas/Proofs.lean` (via Aeneas) and, as RV64IM machine code, in
/// `riscv/AvgRiscv/Proofs.lean`.
///
/// `extern "C"` pins the calling convention to the RISC-V psABI (`a` in `a0`,
/// `b` in `a1`, result in `a0`), which is what the machine-code proof assumes.
#[unsafe(no_mangle)]
pub extern "C" fn avg(a: u64, b: u64) -> u64 {
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
