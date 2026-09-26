import Arm.State

/-!
# `avg` as AArch64 machine code

These are exactly the instruction words rustc emits for `rust/src/lib.rs` (release, target
`aarch64-unknown-linux-gnu`; `aarch64-apple-darwin` is identical). CI recompiles the crate,
disassembles the `avg` symbol, and checks its words against this list: see
`scripts/check-asm.py`. Keep the two in sync.

AAPCS64: arguments in `x0`, `x1`; result in `x0`; return address in `x30` (the link
register). `x8` and `x9` are caller-saved temporaries, so clobbering them is allowed.

Unlike the RISC-V and x86-64 packages, the program is the raw 32-bit words, not a decoded
instruction list: LNSym's `stepi` fetches a word and runs its own decoder
(`decode_raw_inst`), so word decoding is evaluated inside the proof rather than transcribed.
The decoder's agreement with the ISA remains trusted. Comments are for the reader only.
-/

namespace AvgArm

/-- The instruction words of `avg`, in program order (little-endian in the object file). -/
def avgProgram : List (BitVec 32) :=
  [ 0xca000028#32     -- eor x8, x1, x0            x8 := b ^ a
  , 0x8a000029#32     -- and x9, x1, x0            x9 := b & a
  , 0x8b480520#32     -- add x0, x9, x8, lsr #1    x0 := x9 + (x8 >> 1)
  , 0xd65f03c0#32 ]   -- ret                       pc := x30

/-- `code` is loaded at `base` in `s`: LNSym's program map (address ↦ word, which `stepi`
fetches from) holds word `k` at `base + 4k`. It may hold other code too. -/
def CodeAt (s : ArmState) (base : BitVec 64) (code : List (BitVec 32)) : Prop :=
  ∀ k (hk : k < code.length), s.program.find? (base + BitVec.ofNat 64 (4 * k)) = some code[k]

/-- The LNSym program map holding just `code`, word `k` at `base + 4k`. -/
def loadAt (base : BitVec 64) (code : List (BitVec 32)) : Program :=
  code.mapIdx fun k word => (base + BitVec.ofNat 64 (4 * k), word)

end AvgArm
