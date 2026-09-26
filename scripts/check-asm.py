#!/usr/bin/env python3
"""Check that rustc's machine code for `avg` is exactly the instruction list each proof is about.

Each ISA proof (riscv/AvgRiscv/Proofs.lean, x86/AvgX86/Proofs.lean) is about a Lean list
`avgProgram` in the package's `Impl.lean`. This script ties that list to real compiler output:

  1. build rust/ for the ISA's target (release),
  2. disassemble the `avg` symbol with objdump,
  3. render each instruction in the Lean model's syntax and compare with `avgProgram`.

Trusted here: rustc, objdump, and this script's mnemonic mapping. Replacing the text
comparison with a proof about the raw bytes (a verified decoder) is tracked in TODO.md.

rustc is pinned (RUST_TOOLCHAIN): codegen can change between versions and each proof is
about one exact instruction sequence. Bumping it may require updating the Impl files.

Usage: scripts/check-asm.py [riscv|x86 ...]   (default: all; run from anywhere)
Needs: rustup with RUST_TOOLCHAIN and each ISA's target installed; the ISA's objdump.
Env:   OBJDUMP_RISCV (default riscv64-unknown-elf-objdump), OBJDUMP_X86 (default objdump)
"""

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CRATE = os.path.join(ROOT, "rust")
RUST_TOOLCHAIN = "1.94.0"
SYMBOL = "avg"


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, text=True, capture_output=True, **kw).stdout


def build_rlib(target, rustflags=""):
    """Build the crate's rlib (an `ar` archive of the object files) and return its path."""
    target_dir = os.path.join(CRATE, "target", "asm-check")  # isolated from normal builds
    env = dict(os.environ, RUSTFLAGS=rustflags, RUSTUP_TOOLCHAIN=RUST_TOOLCHAIN)
    subprocess.run(
        ["cargo", "build", "--quiet", "--release", "--lib", "--target", target,
         "--target-dir", target_dir],
        cwd=CRATE, env=env, check=True,
    )
    rlib = os.path.join(target_dir, target, "release", "libavg.rlib")
    if not os.path.exists(rlib):
        sys.exit(f"missing {rlib}")
    return rlib


def objdump_lines(objdump, flags, obj):
    """(raw hex bytes, mnemonic, operand string) for each instruction of SYMBOL."""
    out = run([objdump, "-d", *flags, f"--disassemble={SYMBOL}", obj])
    insns = []
    for line in out.splitlines():
        # riscv: "   0:\t00a5f633          \tand\tx12,x11,x10"
        # x86:   "   0:\t48 89 f0             \tmov    rax,rsi"
        m = re.match(r"^\s*[0-9a-f]+:\s+((?:[0-9a-f]{2,8} ?)+)\s+(\S+)\s*(.*?)\s*(#.*)?$", line)
        if m:
            insns.append((m.group(1).replace(" ", ""), m.group(2), m.group(3)))
    if not insns:
        sys.exit(f"symbol `{SYMBOL}` not found in {obj}")
    return insns


def lean_list(path, name="avgProgram"):
    """The entries of `def <name> : List Instr := [ ... ]`, whitespace-normalised.

    Entries are split at top-level commas only (x86lean entries `⟨op, len⟩` contain commas)."""
    src = open(path).read()
    m = re.search(rf"def {name} : List Instr :=\s*\[", src)
    if not m:
        sys.exit(f"could not find `def {name} : List Instr := [` in {path}")
    src = re.sub(r"--[^\n]*", "", src[m.end():])
    entries, cur, depth = [], "", 0
    for ch in src:
        if ch in "[(⟨":
            depth += 1
        elif ch in "])⟩":
            if depth == 0:  # the list's closing `]`
                break
            depth -= 1
        if ch == "," and depth == 0:
            entries.append(cur)
            cur = ""
        else:
            cur += ch
    entries.append(cur)
    return [" ".join(e.split()) for e in entries if e.strip()]


# ---------------------------------------------------------------------------------------------
# RISC-V: riscv-zkvm's `Instr` (RV64IM: no compressed or atomic instructions)
# ---------------------------------------------------------------------------------------------

RISCV_FORMATS = {  # objdump mnemonic -> (Lean constructor, operand kinds). r = reg, i = imm.
    "add": ("ADD", "rrr"), "sub": ("SUB", "rrr"), "and": ("AND", "rrr"),
    "or": ("OR", "rrr"), "xor": ("XOR", "rrr"), "sll": ("SLL", "rrr"),
    "srl": ("SRL", "rrr"), "sra": ("SRA", "rrr"), "slt": ("SLT", "rrr"),
    "sltu": ("SLTU", "rrr"), "mul": ("MUL", "rrr"),
    "addi": ("ADDI", "rri"), "andi": ("ANDI", "rri"), "ori": ("ORI", "rri"),
    "xori": ("XORI", "rri"), "slli": ("SLLI", "rri"), "srli": ("SRLI", "rri"),
    "srai": ("SRAI", "rri"),
}


def riscv_to_lean(raw, mnem, ops):
    if len(raw) != 8:
        sys.exit(f"compressed instruction in output (not RV64IM): {mnem} {ops}")
    ops = [o.strip() for o in ops.split(",")] if ops else []

    def reg(o):
        if not re.fullmatch(r"x([0-9]|[12][0-9]|3[01])", o):
            sys.exit(f"bad register {o}")
        return "." + o

    if mnem == "jalr":  # "x0,0(x1)"
        rd, rest = ops
        m = re.fullmatch(r"(-?\d+)\((x\d+)\)", rest)
        if not m:
            sys.exit(f"cannot parse jalr operands {ops}")
        return f".JALR {reg(rd)} {reg(m.group(2))} {int(m.group(1))}"
    if mnem not in RISCV_FORMATS:
        sys.exit(f"instruction `{mnem} {','.join(ops)}` has no mapping to riscv-zkvm's Instr")
    ctor, kinds = RISCV_FORMATS[mnem]
    if len(ops) != len(kinds):
        sys.exit(f"`{mnem}` expects {len(kinds)} operands, got {ops}")
    return f".{ctor} " + " ".join(reg(o) if k == "r" else str(int(o, 0)) for o, k in zip(ops, kinds))


def check_riscv():
    rlib = build_rlib("riscv64imac-unknown-none-elf", "-C target-feature=-c,-zca,-a")
    objdump = os.environ.get("OBJDUMP_RISCV", "riscv64-unknown-elf-objdump")
    compiled = [riscv_to_lean(*i) for i in objdump_lines(objdump, ["-M", "no-aliases,numeric"], rlib)]
    return compiled, lean_list(os.path.join(ROOT, "riscv", "AvgRiscv", "Impl.lean"))


# ---------------------------------------------------------------------------------------------
# x86-64: x86lean's `Instr` = ⟨op, encoded length⟩ (64-bit GPR forms only)
# ---------------------------------------------------------------------------------------------

X86_GPRS = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
            "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"}
X86_BIN = {"add", "sub", "and", "or", "xor", "cmp", "test", "adc", "sbb"}
X86_SHIFT = {"shl", "shr", "sar"}


def x86_to_lean(raw, mnem, ops):
    """Only 64-bit register-register / register-imm8 forms; anything else is refused."""
    length = len(raw) // 2
    ops = [o.strip() for o in ops.split(",")] if ops else []

    def reg(o):
        if o not in X86_GPRS:
            sys.exit(f"unsupported x86 operand `{o}` in `{mnem} {','.join(ops)}` (64-bit GPRs only)")
        return f"(.reg .{o})"

    if mnem == "ret" and not ops:
        body = ".ret"
    elif mnem == "mov" and len(ops) == 2:
        body = f".mov .q {reg(ops[0])} {reg(ops[1])}"
    elif mnem in X86_BIN and len(ops) == 2:
        body = f".bin .{mnem} .q {reg(ops[0])} {reg(ops[1])}"
    elif mnem in X86_SHIFT and len(ops) == 2 and re.fullmatch(r"(0x)?[0-9a-f]+", ops[1]):
        body = f".shift .{mnem} .q {reg(ops[0])} (.imm8 {int(ops[1], 0)})"
    else:
        sys.exit(f"instruction `{mnem} {','.join(ops)}` has no mapping to x86lean's Instr")
    return f"⟨{body}, {length}⟩"


def check_x86():
    rlib = build_rlib("x86_64-unknown-linux-gnu")
    objdump = os.environ.get("OBJDUMP_X86", "objdump")
    compiled = [x86_to_lean(*i) for i in objdump_lines(objdump, ["-M", "intel"], rlib)]
    impl = os.path.join(ROOT, "x86", "AvgX86", "Impl.lean")
    # avgProgram = avgBody ++ [⟨.ret, 1⟩]: compare against the body list plus that final entry.
    src = open(impl).read()
    tail = re.search(r"def avgProgram : List Instr :=\s*avgBody \+\+ \[(.*?)\]", src, re.S)
    if not tail:
        sys.exit(f"could not find `def avgProgram := avgBody ++ [...]` in {impl}")
    expected = lean_list(impl, "avgBody") + [" ".join(tail.group(1).split())]
    return compiled, expected


ISAS = {"riscv": check_riscv, "x86": check_x86}


def main():
    wanted = sys.argv[1:] or list(ISAS)
    failed = []
    for isa in wanted:
        if isa not in ISAS:
            sys.exit(f"unknown ISA `{isa}`; choose from {', '.join(ISAS)}")
        compiled, expected = ISAS[isa]()
        print(f"== {isa}")
        for i in range(max(len(compiled), len(expected))):
            c = compiled[i] if i < len(compiled) else "<none>"
            e = expected[i] if i < len(expected) else "<none>"
            print(f"{'  ' if c == e else '!!'} {i:2}  rustc: {c:44}  lean: {e}")
        if compiled != expected:
            failed.append(isa)
            print(f"rustc's `{SYMBOL}` differs from the {isa} avgProgram. Update the Impl file to match "
                  "(the proof must then be redone).", file=sys.stderr)
        else:
            print(f"OK: rustc's `{SYMBOL}` is exactly the {isa} avgProgram ({len(expected)} instructions).")
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()
