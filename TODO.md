# TODO

## RISC-V: take objdump out of the trusted base (option b)

Today `backends/riscv/AvgRiscv/Proofs.lean` proves the instruction list `avgProgram` correct, and
`scripts/check-asm.py` ties that list to rustc's output by disassembling it with
objdump and comparing text. So objdump, and the script's mnemonic-to-`Instr` mapping,
are trusted.

Replace that with a proof about the bytes:

- [ ] Extract the raw bytes of the `avg` symbol from the rlib/object and commit them as a
      Lean constant, e.g. `avgBytes : List (BitVec 32)` = `[0x00a5f633, 0x00a5c533, ...]`.
      CI checks the committed bytes against a fresh build (a byte compare, no disassembler).
- [ ] Prove `avgBytes.map decode = avgProgram.map some` using riscv-zkvm's decoder
      (`RiscvZkvm.Interpreter.Decode`), ideally by `decide`.
- [ ] Better: state the theorem over a code memory loaded from the bytes, so the
      `Instr` list is an internal detail rather than the object of the proof.
- [ ] Check what the decoder itself is trusted for. If it isn't proved against Sail's
      `encdec`, prove or cite that as well.

## RISC-V: lift the result to the Sail model

`avgProgram_correct` is about riscv-zkvm's hand-written `stepN`. Its agreement with the
Sail RISC-V spec is per instruction (`RiscvZkvm.Rv64.SailEquiv`).

- [ ] Use `sailStepN_run_sim` to restate the theorem over `RiscvZkvm.Sail` states, so
      the trusted model is Sail rather than the hand-written `stepN`.

## x86-64: take objdump out of the trusted base

`backends/x86/AvgX86/Impl.lean` passes the AT&T assembly for the complete `avg` function to
Kraken's parser. `scripts/check-asm.py` checks that text against rustc's disassembly,
preserving operand widths and instruction count while normalizing GNU spelling.
Kraken has an assembly parser, not a binary decoder; this remains a trusted text binding.

- [ ] Add a binary-decoding path with a proved connection to Kraken's parsed program.
      Then commit `avg`'s bytes (`48 89 f0 48 21 f8 …`) and prove they decode to
      `avgProgram`, replacing disassembly/text comparison with direct byte extraction.

## x86-64: what the model is trusted for

Kraken's semantics are handwritten. Upstream's native differential-test harness assembles
AT&T test programs with GNU binutils and compares modeled register/flag results against
host execution; this is not a proof of ISA equivalence, nor a hardware-validation result
established by this repository's CI. The model revision is pinned in
[`backends/x86/lakefile.toml`](backends/x86/lakefile.toml), and its Lean toolchain in
[`backends/x86/lean-toolchain`](backends/x86/lean-toolchain).
It does not model segment registers/bases, virtual memory, canonical-address checks, or
most exceptions/faults. Our full-function theorem establishes the loaded stack return
address, stack pop, result and memory/vector/GPR frame, not guarantees for those omissions.

- [ ] Run and record the pinned upstream native differential tests on supported hardware,
      especially the instruction forms used here; do not confuse passing tests with proof.
- [ ] Track a formal connection to an authoritative x86 ISA specification.
- [ ] Rebuild the full proof and recheck compiler binding whenever changing Kraken's pin
      or the nightly Lean toolchain.

## AArch64: stabilize the model pin and byte extraction

`backends/arm/` uses LNSym's fetch/decode/run semantics on raw instruction words. Decoding those
words is checked in Lean, but the hand-written decoder and instruction semantics are
still trusted to describe AArch64. Upstream has co-simulation tooling; this repository
does not establish an ASL equivalence or claim local Arm hardware validation.

- [ ] Move the LNSym pin in [`backends/arm/lakefile.toml`](backends/arm/lakefile.toml)
      to an upstream main/tag revision once the Lean upgrade lands, rebuilding the proof
      before changing it.
- [ ] Replace objdump word extraction with direct extraction of the `avg` symbol's bytes.
      Today objdump and the extraction/comparison script remain trusted.
- [ ] Track an ASL equivalence for the decoder and the instruction forms used here.
- [ ] Consider a separation-logic wrapper for composition with callers. The current theorem
      already preserves memory, the separate program map and all state fields except
      `x0`, `x8`, `x9` and PC; it does not model self-modifying code.
