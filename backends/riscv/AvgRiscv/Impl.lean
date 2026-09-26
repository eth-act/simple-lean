import RiscvZkvm.Rv64

/-!
# `avg` as RV64IM machine code

These are exactly the instructions rustc emits for `impl/rust/src/lib.rs` (release, target
`riscv64imac-unknown-none-elf` with compressed instructions disabled). CI recompiles the
crate, disassembles the `avg` symbol, and checks it against this list:
see `scripts/check-asm.py`. Keep the two in sync; do not edit one without the other.

RISC-V psABI: arguments in `a0` (x10) and `a1` (x11), result in `a0`, return address in
`ra` (x1). `x12` (a2) is a caller-saved temporary.
-/

namespace AvgRiscv

open RiscvZkvm.Rv64

/-- The body of `avg`, in program order. -/
def avgProgram : List Instr :=
  [ .AND  .x12 .x11 .x10       -- and  a2, a1, a0     a2 := b & a
  , .XOR  .x10 .x11 .x10       -- xor  a0, a1, a0     a0 := b ^ a
  , .SRLI .x10 .x10 1          -- srli a0, a0, 1      a0 := a0 >> 1
  , .ADD  .x10 .x12 .x10       -- add  a0, a2, a0     a0 := a2 + a0
  , .JALR .x0  .x1  0 ]        -- ret                 pc := ra
end AvgRiscv
