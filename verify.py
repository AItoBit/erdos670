"""Compile the complete proof sequentially with the pinned Lean toolchain."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")

root = Path(__file__).resolve().parent
environment = os.environ.copy()
environment["LEAN_NUM_THREADS"] = "1"
modules = [
    "DiameterConstruction.Defs",
    "DiameterConstruction.Singer",
    "DiameterConstruction.Analysis",
    "DiameterConstruction.Construction",
    "DiameterConstruction.Fourier",
    "DiameterConstruction.Profile",
    "DiameterConstruction.Realization",
    "DiameterConstruction.DiscreteProfile",
    "DiameterConstruction.Scaling",
    "DiameterConstruction.MainTheorem",
    "DiameterConstruction.RepositoryBridge",
    "DiameterConstruction",
]
previous = json.loads((root / "verification.json").read_text(encoding="utf-8")) if (root / "verification.json").exists() else []
records = []
reuse_prefix = True
with (root / "verification.log").open("a", encoding="utf-8") as log:
    for module in modules:
        source = Path(module.replace(".", "/") + ".lean")
        output = Path(".lake/build/lib/lean") / source.with_suffix(".olean")
        (root / output).parent.mkdir(parents=True, exist_ok=True)
        source_hash = hashlib.sha256((root / source).read_bytes()).hexdigest()
        if reuse_prefix and len(previous) > len(records):
            old = previous[len(records)]
            if old["module"] == module and old["exit_code"] == 0 and old["sha256"] == source_hash and (root / output).exists():
                records.append(old)
                print("Previously compiled, source unchanged: " + module, flush=True)
                continue
        reuse_prefix = False
        command = ["lake", "env", "lean", "-DwarningAsError=true", str(source), "-o", str(output)]
        print("Compiling " + module, flush=True)
        result = subprocess.run(command, cwd=root, env=environment, text=True,
                                encoding="utf-8", errors="replace", capture_output=True)
        text = result.stdout + result.stderr
        log.write(json.dumps(command) + "\n" + text + "\nEXIT " + str(result.returncode) + "\n")
        log.flush()
        records.append({"module": module, "command": command, "exit_code": result.returncode,
                        "sha256": hashlib.sha256((root / source).read_bytes()).hexdigest()})
        (root / "verification.json").write_text(json.dumps(records, indent=2), encoding="utf-8")
        if result.returncode:
            print(text, flush=True)
            sys.exit(result.returncode)
        print("PASS " + module, flush=True)
    command = ["lake", "env", "lean", "-DwarningAsError=true", "Verification.lean"]
    print("Checking statements and axioms", flush=True)
    result = subprocess.run(command, cwd=root, env=environment, text=True,
                            encoding="utf-8", errors="replace", capture_output=True)
    text = result.stdout + result.stderr
    log.write(json.dumps(command) + "\n" + text + "\nEXIT " + str(result.returncode) + "\n")
    print(text, flush=True)
    sys.exit(result.returncode)
