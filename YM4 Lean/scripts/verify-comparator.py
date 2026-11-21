"""Compare the public Wilson statement with the solution using the native Lake APIs."""

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
ADAPTER = ROOT / "scripts" / "comparator"
PUBLIC_ROOT = "YangMills.wilson_subsequence"
CONSTRUCTION_ROOT = "YangMills.su2_fixed_observable_continuum_limit"
CHALLENGE_ROOTS = (PUBLIC_ROOT, "propext", "Classical.choice", "Quot.sound",
                   "Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Eq")
SCOPE_SHA256 = "cbaa20dfb609daa84df79f6a1ecff714d68c1184755fc419fe43d19cc2558ec8"


def create_scope(work):
    with gzip.open(ADAPTER / "scope.json.gz", "rb") as f:
        data = f.read()
    if hashlib.sha256(data).hexdigest() != SCOPE_SHA256:
        raise ValueError("The bundled scope differs from the recorded Wilson scope.")
    path = work / "scope.json"
    path.write_bytes(data)
    return path


def export(args, output, cwd, env=None):
    with output.open("xb") as out:
        subprocess.run(args, cwd=cwd, env=env, stdout=out, check=True)
    with output.open("rb") as f:
        meta = json.loads(f.readline())["meta"]
    if meta["lean"]["version"] != "4.33.1" or meta["format"]["version"] != "3.1.0":
        raise ValueError(f"Expected Lean 4.33.1 and NDJSON 3.1.0 in {output}")


def export_challenge(exporter, work, module):
    # Expose only the pinned dependency packages to this separate Lean process.
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = ROOT / manifest["packagesDir"]
    libs = [packages / p["name"] / ".lake/build/lib/lean" for p in manifest["packages"]]
    if not (packages / "mathlib/.lake/build/lib/lean/Mathlib.olean").is_file():
        raise ValueError("Fetch the Mathlib cache in the trusted project first (lake exe cache get).")
    prefix = subprocess.check_output(["lean", "--print-prefix"],
                                     cwd=ROOT, text=True).strip()
    tool_bin = Path(prefix).resolve() / "bin"
    env = os.environ.copy()
    env.pop("LEAN_SYSROOT", None)
    env.pop("LEAN_SRC_PATH", None)
    env["PATH"] = os.pathsep.join((str(tool_bin), env.get("PATH", "")))
    iso = work / "challenge"
    source = Path(*module.split(".")).with_suffix(".lean")
    (iso / source.parent).mkdir(parents=True)
    shutil.copyfile(ROOT / source, iso / source)
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in libs)
    lean = tool_bin / ("lean.exe" if os.name == "nt" else "lean")
    subprocess.run([lean, "-o", source.with_suffix(".olean"), source],
                   cwd=iso, env=env, check=True)
    env["LEAN_PATH"] = os.pathsep.join((str(iso), env["LEAN_PATH"]))
    output = work / "Challenge.ndjson"
    export([exporter, module, "--", *CHALLENGE_ROOTS], output, iso, env)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--exporter", type=Path, help="lean4export binary built with Lean 4.33.1")
    inputs.add_argument("--exports", type=Path, nargs=2, metavar=("CHALLENGE", "SOLUTION"),
                        help="compare two already-exported NDJSON files")
    parser.add_argument("--candidate", type=Path, help="solution project (default: this repository)")
    parser.add_argument("--work", type=Path, help="parent directory for a new verification run")
    args = parser.parse_args()
    if args.candidate and args.exports:
        parser.error("--candidate applies only when creating new exports")
    if args.work:
        args.work.mkdir(exist_ok=True, parents=True)
    work = Path(tempfile.mkdtemp(prefix="wilson-comparator-", dir=args.work)).resolve()
    print(f"Verification files: {work}", flush=True)
    scope = create_scope(work)
    if args.exports:
        challenge, solution = [p.resolve(strict=True) for p in args.exports]
    else:
        exporter = args.exporter
        if os.name == "nt" and not exporter.is_file() and not exporter.suffix:
            exporter = exporter.with_suffix(".exe")
        exporter = exporter.resolve(strict=True)
        candidate = (args.candidate or ROOT).resolve(strict=True)
        config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
        challenge = export_challenge(exporter, work, config["challenge_module"])
        module = config["solution_module"]
        subprocess.run(["lake", "build", f"+{module}:leanArts"], cwd=candidate, check=True)
        solution = work / "Solution.ndjson"
        export(["lake", "env", exporter, module, "--", CONSTRUCTION_ROOT, PUBLIC_ROOT],
               solution, candidate)
    subprocess.run(["lake", "exe", "compare_source_statements", challenge, solution, scope],
                   cwd=ADAPTER, check=True)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
