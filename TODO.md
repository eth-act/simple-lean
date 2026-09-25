# TODO

## RISC-V: take objdump out of the trusted base (option b)

Today `riscv/AvgRiscv/Proofs.lean` proves the instruction list `avgProgram` correct, and
`scripts/check-riscv-asm.py` ties that list to rustc's output by disassembling it with
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
