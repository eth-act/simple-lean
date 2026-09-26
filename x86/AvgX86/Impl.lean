import X86

/-!
# `avg` as x86-64 machine code

These are exactly the instructions rustc emits for `rust/src/lib.rs` (release, target
`x86_64-unknown-linux-gnu`). CI recompiles the crate, disassembles the `avg` symbol, and
checks it against this list: see `scripts/check-asm.py`. Keep the two in sync.

System V AMD64 ABI: arguments in `rdi`, `rsi`; result in `rax`; return address on the stack
at `[rsp]`. `rsi` is caller-saved, so clobbering it is allowed.

Each entry is x86lean's decoded form plus its encoded length in bytes; the length drives
`rip`. The bytes-to-form step is trusted (x86lean has no decoder yet; see TODO.md).
-/

namespace AvgX86

open X86

/-- The body of `avg`, in program order, without the final `ret`. -/
def avgBody : List Instr :=
  [ ⟨.mov .q (.reg .rax) (.reg .rsi), 3⟩            -- 48 89 f0   mov rax, rsi
  , ⟨.bin .and .q (.reg .rax) (.reg .rdi), 3⟩       -- 48 21 f8   and rax, rdi
  , ⟨.bin .xor .q (.reg .rsi) (.reg .rdi), 3⟩       -- 48 31 fe   xor rsi, rdi
  , ⟨.shift .shr .q (.reg .rsi) (.imm8 1), 3⟩       -- 48 d1 ee   shr rsi, 1
  , ⟨.bin .add .q (.reg .rax) (.reg .rsi), 3⟩ ]     -- 48 01 f0   add rax, rsi

/-- The whole function: the body, then `ret`. -/
def avgProgram : List Instr :=
  avgBody ++ [⟨.ret, 1⟩]                            -- c3         ret

end AvgX86
