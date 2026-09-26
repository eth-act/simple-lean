module

public import Kraken.X64.Parser
public import Kraken.X64.OmniSemantics

@[expose] public section

/-!
# rustc's x86-64 assembly for `avg`

System V ABI: arguments in `rdi`, `rsi`, result in `rax`. The compiler-binding check
compares this AT&T assembly with the pinned compiler's disassembly, including `ret`.
Kraken parses assembly, not machine bytes: objdump and this binding remain trusted.
-/

namespace AvgX86

open Kraken.X64.Parser

def avgProgram : Program := parse("
  movq %rsi, %rax
  andq %rdi, %rax
  xorq %rdi, %rsi
  shrq $1, %rsi
  addq %rsi, %rax
  ret
")

end AvgX86
