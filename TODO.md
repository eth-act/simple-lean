# TODO

## RISC-V: take objdump out of the trusted base (option b)

Today `backends/riscv/AvgRiscv/Proofs.lean` proves the instruction list `avgProgram` correct, and
`scripts/check-asm.py` ties that list to rustc's output by disassembling it with
objdump and comparing text. So objdump, and the script's mnemonic-to-`Instr` mapping,
are trusted.

The Lean-authoritative export path now derives words from `avgProgram` and proves
`avgWords.map decode = avgProgram.map some`, plus a byte-serialization roundtrip,
in `backends/riscv/AvgRiscv/Encode.lean`. It does not require rustc or objdump.
For the separate Rust-output comparison:

- [ ] Compare the Rust object's raw symbol bytes with the Lean-exported bytes, replacing
      the mnemonic comparison without maintaining another instruction-word constant.
- [ ] Better: state the theorem over a code memory loaded from the bytes, so the
      `Instr` list is an internal detail rather than the object of the proof.
- [ ] Prove the executable decoder agrees with Sail's `encdec`; upstream currently
      documents that this equivalence is missing.

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
The independent Lean export route instead trusts Kraken's printer and the assembler;
the same binary-decoding gap applies to connecting those emitted bytes to the proof.

- [ ] Add a binary-decoding path with a proved connection to Kraken's parsed program.
      Then commit `avg`'s bytes (`48 89 f0 48 21 f8 …`) and prove they decode to
      `avgProgram`, replacing disassembly/text comparison with direct byte extraction.

## x86-64: what the model is trusted for

Kraken's semantics are handwritten. Upstream's native differential-test harness assembles
AT&T test programs with GNU binutils and compares modeled register/flag results against
host execution; this is not a proof of ISA equivalence, nor a hardware-validation result
established by this repository's CI. The model revision is pinned in
[`tooling/x86/lakefile.toml`](tooling/x86/lakefile.toml), and its Lean toolchain in
[`tooling/x86/lean-toolchain`](tooling/x86/lean-toolchain).
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

- [ ] Move the LNSym pin in [`tooling/arm/lakefile.toml`](tooling/arm/lakefile.toml)
      to an upstream main/tag revision once the Lean upgrade lands, rebuilding the proof
      before changing it.
- [ ] Replace objdump word extraction in the Rust-output comparison with direct extraction
      of the `avg` symbol's bytes. The Lean-authoritative exporter already emits raw words
      without objdump, but still trusts serialization/evaluation and the consumer's assembler.
- [ ] Track an ASL equivalence for the decoder and the instruction forms used here.
- [ ] Consider a separation-logic wrapper for composition with callers. The current theorem
      already preserves memory, the separate program map and all state fields except
      `x0`, `x8`, `x9` and PC; it does not model self-modifying code.
