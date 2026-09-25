#!/usr/bin/env python3
"""Check that rustc's RISC-V output for `avg` is exactly `avgProgram` in riscv/AvgRiscv/Impl.lean.

The Lean proof (riscv/AvgRiscv/Proofs.lean) is about the instruction list `avgProgram`.
This script ties that list to real compiler output:

  1. build rust/ for riscv64 (release, compressed instructions disabled),
  2. disassemble the `avg` symbol with objdump (`-M no-aliases,numeric`: base
     mnemonics, x0..x31 register names),
  3. render each instruction as Lean `Instr` syntax and compare with `avgProgram`.

Trusted here: rustc, objdump, and this script. Removing objdump from the trusted base
(prove the decoder maps the bytes to `avgProgram`) is tracked in TODO.md.

rustc is pinned (RUST_TOOLCHAIN below): codegen can change between versions and the
proof is about one exact instruction sequence. Bumping it may require updating avgProgram.

Usage: scripts/check-riscv-asm.py   (from anywhere)
Needs: rustup with RUST_TOOLCHAIN and target TARGET installed; a RISC-V objdump.
Env:   OBJDUMP (default riscv64-unknown-elf-objdump)
"""

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CRATE = os.path.join(ROOT, "rust")
LEAN_PROGRAM = os.path.join(ROOT, "riscv", "AvgRiscv", "Impl.lean")
RUST_TOOLCHAIN = "1.94.0"
TARGET = "riscv64imac-unknown-none-elf"
# riscv-zkvm models RV64IM: no compressed (C / Zca) or atomic instructions.
RUSTFLAGS = "-C target-feature=-c,-zca,-a"
SYMBOL = "avg"

# objdump mnemonic -> (Lean constructor, operand kinds). r = register, i = immediate.
FORMATS = {
    "add": ("ADD", "rrr"), "sub": ("SUB", "rrr"), "and": ("AND", "rrr"),
    "or": ("OR", "rrr"), "xor": ("XOR", "rrr"), "sll": ("SLL", "rrr"),
    "srl": ("SRL", "rrr"), "sra": ("SRA", "rrr"), "slt": ("SLT", "rrr"),
    "sltu": ("SLTU", "rrr"), "mul": ("MUL", "rrr"),
    "addi": ("ADDI", "rri"), "andi": ("ANDI", "rri"), "ori": ("ORI", "rri"),
    "xori": ("XORI", "rri"), "slli": ("SLLI", "rri"), "srli": ("SRLI", "rri"),
    "srai": ("SRAI", "rri"),
}


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, text=True, capture_output=True, **kw).stdout


def build_object():
    """Build the crate's rlib (an `ar` archive of the object files) and return its path."""
    target_dir = os.path.join(CRATE, "target", "asm-check")  # isolated from normal builds
    env = dict(os.environ, RUSTFLAGS=RUSTFLAGS, RUSTUP_TOOLCHAIN=RUST_TOOLCHAIN)
    cargo = "cargo"
    subprocess.run(
        [cargo, "build", "--quiet", "--release", "--lib", "--target", TARGET,
         "--target-dir", target_dir],
        cwd=CRATE, env=env, check=True,
    )
    rlib = os.path.join(target_dir, TARGET, "release", "libavg.rlib")
    if not os.path.exists(rlib):
        sys.exit(f"missing {rlib}")
    return rlib


def disassemble(obj):
    objdump = os.environ.get("OBJDUMP", "riscv64-unknown-elf-objdump")
    out = run([objdump, "-d", "-M", "no-aliases,numeric", f"--disassemble={SYMBOL}", obj])
    insns = []
    for line in out.splitlines():
        # "   0:\t00a5f633          \tand\tx12,x11,x10"
        m = re.match(r"^\s*[0-9a-f]+:\s+([0-9a-f]+)\s+(\S+)\s*(.*?)\s*(#.*)?$", line)
        if m:
            raw, mnem, ops = m.group(1), m.group(2), m.group(3)
            if len(raw) != 8:
                sys.exit(f"compressed instruction in output (not RV64IM): {line.strip()}")
            insns.append((mnem, [o.strip() for o in ops.split(",")] if ops else []))
    if not insns:
        sys.exit(f"symbol `{SYMBOL}` not found in {obj}")
    return insns


def to_lean(mnem, ops):
    reg = lambda o: "." + o if re.fullmatch(r"x([0-9]|[12][0-9]|3[01])", o) else sys.exit(f"bad register {o}")
    if mnem == "jalr":  # "x0,0(x1)"
        rd, rest = ops
        m = re.fullmatch(r"(-?\d+)\((x\d+)\)", rest)
        if not m:
            sys.exit(f"cannot parse jalr operands {ops}")
        return f".JALR {reg(rd)} {reg(m.group(2))} {int(m.group(1))}"
    if mnem not in FORMATS:
        sys.exit(f"instruction `{mnem} {','.join(ops)}` has no mapping to riscv-zkvm's Instr")
    ctor, kinds = FORMATS[mnem]
    if len(ops) != len(kinds):
        sys.exit(f"`{mnem}` expects {len(kinds)} operands, got {ops}")
    parts = [reg(o) if k == "r" else str(int(o, 0)) for o, k in zip(ops, kinds)]
    return f".{ctor} " + " ".join(parts)


def lean_program():
    src = open(LEAN_PROGRAM).read()
    m = re.search(r"def avgProgram : List Instr :=\s*\[(.*?)\]", src, re.S)
    if not m:
        sys.exit(f"could not find `def avgProgram` in {LEAN_PROGRAM}")
    body = re.sub(r"--[^\n]*", "", m.group(1))
    return [" ".join(i.split()) for i in body.split(",") if i.strip()]


def main():
    compiled = [to_lean(m, o) for m, o in disassemble(build_object())]
    expected = lean_program()
    for i in range(max(len(compiled), len(expected))):
        c = compiled[i] if i < len(compiled) else "<none>"
        e = expected[i] if i < len(expected) else "<none>"
        print(f"{'  ' if c == e else '!!'} {i:2}  rustc: {c:28}  lean: {e}")
    if compiled != expected:
        print("\nrustc's output for `avg` differs from `avgProgram` in riscv/AvgRiscv/Impl.lean.\n"
              "Update avgProgram to match (the proof in riscv/AvgRiscv/Proofs.lean must then be redone).",
              file=sys.stderr)
        sys.exit(1)
    print(f"\nOK: rustc's `{SYMBOL}` is exactly avgProgram ({len(expected)} instructions).")


if __name__ == "__main__":
    main()
