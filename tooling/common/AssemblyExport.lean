import Lean.Data.Json

namespace AssemblyExport

open Lean (toJson)

/-- Supported C signatures. Pointers, aggregates and floating-point values are not supported. -/
inductive Signature where
  | u64_0
  | u64_1
  | u64_2
  deriving DecidableEq, Repr

/-- The client supplies a specification relating the signature and the exact program.
The exporter checks this proof's type, not whether the client's specification is meaningful.
The client remains responsible for an adequate ABI, return and frame contract. -/
structure Function (Program : Type) (contract : Signature → Program → Prop) where
  symbol : String
  signature : Signature
  program : Program
  correct : contract signature program

structure Artifact where
  symbol : String
  target : String
  assembly : String
  header : String

private def identifierStart (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

private def identifierRest (c : Char) : Bool :=
  identifierStart c || ('0' ≤ c && c ≤ '9')

def validSymbol (symbol : String) : Bool :=
  match symbol.toList with
  | [] => false
  | c :: cs => identifierStart c && cs.all identifierRest

private def parameters : Signature → String
  | .u64_0 => "void"
  | .u64_1 => "uint64_t"
  | .u64_2 => "uint64_t, uint64_t"

/-- Render one Linux ELF function and its C/C++ header. The backend supplies only the body. -/
def render {Program : Type} {contract : Signature → Program → Prop}
    (fn : Function Program contract) (target body : String)
    (preamble : String := "") (alignment : Nat := 2) (marker : String := "@") :
    Except String Artifact := do
  if !validSymbol fn.symbol then
    throw "export symbol must be a nonempty ASCII C identifier"
  let guard := "LEAN_EXPORT_" ++ fn.symbol ++ "_H"
  let header := "#ifndef " ++ guard ++ "\n#define " ++ guard ++
    "\n#include <stdint.h>\n#ifdef __cplusplus\nextern \"C\" {\n#endif\nuint64_t " ++
    fn.symbol ++ "(" ++ parameters fn.signature ++
    ");\n#ifdef __cplusplus\n}\n#endif\n#endif\n"
  let assembly := preamble ++ ".text\n.p2align " ++ toString alignment ++
    "\n.globl " ++ fn.symbol ++ "\n.type " ++ fn.symbol ++ ", " ++ marker ++
    "function\n" ++ fn.symbol ++ ":\n" ++ body ++
    ".size " ++ fn.symbol ++ ", .-" ++ fn.symbol ++
    "\n.section .note.GNU-stack,\"\"," ++ marker ++ "progbits\n"
  return { symbol := fn.symbol, target, assembly, header }

/-- Machine-readable protocol consumed by scripts/export.py; diagnostics stay off stdout. -/
def run (artifact : Except String Artifact) : IO Unit := do
  let artifact ← match artifact with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  let stdout ← IO.getStdout
  stdout.putStrLn (Lean.Json.compress (Lean.Json.mkObj [
    ("symbol", toJson artifact.symbol), ("target", toJson artifact.target),
    ("assembly", toJson artifact.assembly), ("header", toJson artifact.header)]))

end AssemblyExport
