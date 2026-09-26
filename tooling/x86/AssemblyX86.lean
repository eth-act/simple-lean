import AssemblyExport
import Kraken.X64.PrintIntel

namespace AssemblyX86

/-- Register-only integer operations; shift immediates must fit their encoding.
Expressions involving instruction positions, labels, or arithmetic are not accepted. -/
private def supportedOperation : Operation .W64 → Bool
  | .mov (.reg _) (.regOrMem (.reg _)) => true
  | .and (.reg _) (.regOrMem (.reg _)) => true
  | .xor (.reg _) (.regOrMem (.reg _)) => true
  | .add (.reg _) (.regOrMem (.reg _)) => true
  | .shr (.reg _) .cl => true
  | .shr (.reg _) (.imm8 (.int64 count)) => decide (0 ≤ count.toInt ∧ count.toInt ≤ 255)
  | _ => false

/-- Export a checked declaration using Kraken's actual Intel-syntax printer.
Only 64-bit, register-only leaf instructions followed by one final `ret` are supported.
All three C signatures are supported; their semantic and ABI obligations belong to
`contract` and the client's proof, not to this syntactic adapter. -/
def emit {contract : AssemblyExport.Signature → Program → Prop}
    (fn : AssemblyExport.Function Program contract) : Except String AssemblyExport.Artifact := do
  let mut lines : Array String := #[]
  let mut returned := false
  for directive in fn.program do
    if returned then
      throw "x86 export rejects instructions or directives after ret"
    match directive with
    | .instr (.regular .W64 .W64 .ret) => returned := true
    | .instr (.regular .W64 .W64 operation) =>
      if !supportedOperation operation then
        throw "x86 export supports only register mov/and/xor/add and register shr with cl or an unsigned 8-bit literal"
    | _ =>
      throw "x86 export rejects non-64-bit instructions, labels, data, and unsupported directives"
    lines := lines.push (toString directive)
  if !returned then
    throw "x86 export requires a final 64-bit ret"
  AssemblyExport.render fn "x86_64-linux-gnu"
    (String.intercalate "\n" lines.toList ++ "\n") ".intel_syntax noprefix\n" 4

end AssemblyX86
