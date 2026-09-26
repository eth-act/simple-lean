# TODO

## RISC-V: take objdump out of the trusted base (option b)

Today `riscv/AvgRiscv/Proofs.lean` proves the instruction list `avgProgram` correct, and
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

Same gap as RISC-V (b): `x86/AvgX86/Impl.lean` is a transcription of objdump's output,
checked textually by `scripts/check-asm.py`. x86lean has no decoder yet (it trusts Intel
XED; its own roadmap has a Lean decoder "for the covered subset" as a later phase).

- [ ] When x86lean ships its decoder, commit `avg`'s bytes (`48 89 f0 48 21 f8 …`) and
      prove they decode to `avgProgram`, replacing the text comparison.

## x86-64: what the model is trusted for

x86lean's `step` is hand-written, differentially tested against ACL2 x86isa (every form,
zero unexplained disagreements), not proved against it, and not yet co-simulated on
hardware. It is three weeks old and pinned to one commit in `x86/lakefile.toml`.

- [ ] Re-pin when x86lean runs hardware co-simulation; check the AST didn't move.
- [ ] Watch for a Sail/x86isa-backed Lean model (the Sail x86 model's Lean output did not
      build under lean-sail v6: old memory interface) that could replace or check it.

## AArch64: stabilize the model pin and byte extraction

`arm/` uses LNSym's fetch/decode/run semantics on raw instruction words. Decoding those
words is checked in Lean, but the hand-written decoder and instruction semantics are
still trusted to describe AArch64. Upstream has co-simulation tooling; this repository
does not establish an ASL equivalence or claim local Arm hardware validation.

- [ ] Move the exact `upgrade-lean-versions` commit pin to an upstream main/tag revision
      once the Lean upgrade lands, rebuilding the proof before changing it.
- [ ] Replace objdump word extraction with direct extraction of the `avg` symbol's bytes.
      Today objdump and the extraction/comparison script remain trusted.
- [ ] Track an ASL equivalence for the decoder and the instruction forms used here.
- [ ] Consider a separation-logic wrapper for composition with callers. The current theorem
      already preserves memory, the separate program map and all state fields except
      `x0`, `x8`, `x9` and PC; it does not model self-modifying code.
