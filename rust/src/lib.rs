#![cfg_attr(not(test), no_std)]

/// Floor average of two `u64`s without overflow.
///
/// `a + b = 2·(a & b) + (a ^ b)`, so `(a + b) / 2 = (a & b) + (a ^ b) / 2`,
/// and neither term can overflow. Proved to satisfy the spec `Avg.IsAvg` in
/// `aeneas/AvgAeneas/Proofs.lean` (via Aeneas) and as machine code in
/// `riscv/AvgRiscv/Proofs.lean`, `x86/AvgX86/Proofs.lean`, `arm/AvgArm/Proofs.lean`.
///
/// `extern "C"` selects each target's C ABI: RISC-V psABI, x86-64 System V,
/// or AAPCS64. The machine-code proofs use the corresponding argument/result registers.
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
