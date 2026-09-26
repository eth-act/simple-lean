#!/usr/bin/env python3
"""Build any Lake package's checked exporter and write its assembly/header pair.

Usage: python3 scripts/export.py --package path/to/package --export MyLibrary.Export --out-dir dist
The module must expose a root `main : IO Unit` using AssemblyExport.run. Only Python
and Lake/elan are needed. Run toolchain-incompatible packages sequentially.
"""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


def export(package, module, output):
    subprocess.run(["lake", "build"], cwd=package, check=True)
    subprocess.run(["lake", "build", module], cwd=package, check=True)
    # Import the built module rather than assuming a source layout or re-parsing its file.
    with tempfile.TemporaryDirectory(prefix="lean-export-") as temporary:
        launcher = Path(temporary) / "RunExport.lean"
        launcher.write_text(f"import {module}\n")
        result = subprocess.run(["lake", "env", "lean", "--run", str(launcher)],
                                cwd=package, check=True, text=True, capture_output=True)
    artifact = json.loads(result.stdout)
    if not isinstance(artifact, dict) or set(artifact) != {"symbol", "target", "assembly", "header"}:
        raise ValueError("exporter must emit an AssemblyExport artifact object")
    if any(not isinstance(value, str) or not value for value in artifact.values()):
        raise ValueError("artifact fields must be nonempty strings")
    symbol = artifact["symbol"]
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", symbol):
        raise ValueError("export symbol must be an ASCII C identifier")
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".lean-export-", dir=output) as temporary:
        stage = Path(temporary)
        for suffix, field in [("s", "assembly"), ("h", "header")]:
            (stage / f"{symbol}.{suffix}").write_text(artifact[field])
        for suffix in ["s", "h"]:
            os.replace(stage / f"{symbol}.{suffix}", output / f"{symbol}.{suffix}")
    print(f"Exported {symbol}.s and {symbol}.h for {artifact['target']} to {output}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", required=True, type=Path, help="Lake package directory")
    parser.add_argument("--export", dest="module", default="Export", help="exporter module (default: Export)")
    parser.add_argument("--out-dir", type=Path, default=Path("dist"))
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", args.module):
        parser.error("--export must be a dot-separated Lean module name")
    package = args.package.resolve()
    if not any((package / name).is_file() for name in ["lakefile.toml", "lakefile.lean"]):
        parser.error("--package must contain lakefile.toml or lakefile.lean")
    try:
        export(package, args.module, args.out_dir.resolve())
    except subprocess.CalledProcessError as error:
        parser.exit(1, f"command failed: {error.cmd}\n{error.stdout or ''}{error.stderr or ''}\n")
    except (ValueError, OSError) as error:
        parser.exit(1, f"export failed: {error}\n")


if __name__ == "__main__":
    main()
