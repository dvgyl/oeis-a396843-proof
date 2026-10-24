#!/usr/bin/env python3
"""Fetch the locked Lean dependencies and the required Mathlib cache."""

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable or absolute path")
    args = parser.parse_args()
    lake = shutil.which(args.lake)
    if lake is None:
        parser.error("Lake is unavailable. Install Elan or use --lake with an absolute path.")
    project = Path(__file__).resolve().parents[1] / "lean"
    manifest = project / "lake-manifest.json"
    locked = manifest.read_bytes()
    imports = sorted({
        name
        for path in (project / "Hanna").rglob("*.lean")
        for name in re.findall(r"^import (Mathlib\.[\w.]+)$", path.read_text(), re.MULTILINE)
    })
    env = os.environ.copy()
    env["PATH"] = str(Path(lake).parent) + os.pathsep + env.get("PATH", "")
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    commands = [
        [lake, "build", "+Cache.Main"],
        [lake, "env", "lean", "--run", ".lake/packages/mathlib/Cache/Main.lean", "get", *imports],
    ]
    for command in commands:
        print("Command:", " ".join(command), flush=True)
        subprocess.run(command, cwd=project, env=env, check=True)
    if manifest.read_bytes() != locked:
        raise SystemExit("Dependency setup changed lake-manifest.json. Review the change before building.")
    print("Dependency setup passed. The lockfile is unchanged.")


if __name__ == "__main__":
    main()
