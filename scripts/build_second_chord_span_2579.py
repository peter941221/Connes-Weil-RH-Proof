"""Synchronize the 2579 import closure and build its audit in a Linux mirror."""
import argparse
from pathlib import Path
import subprocess

from generate_second_chord_span_2579 import ROOT, AUDIT


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror", type=Path, required=True)
    parser.add_argument("--lake", type=Path, required=True)
    args = parser.parse_args()
    mirror = args.mirror.resolve()
    assert mirror != ROOT.resolve()
    for relative in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        assert (ROOT / relative).read_bytes() == (mirror / relative).read_bytes(), relative
    pending, copied = ["ConnesWeilRH.Dev." + AUDIT], set()
    while pending:
        module = pending.pop()
        relative = module.replace(".", "/") + ".lean"
        if relative in copied:
            continue
        copied.add(relative)
        data = (ROOT / relative).read_bytes()
        target = mirror / relative
        assert target.resolve().is_relative_to(mirror)
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_bytes() != data:
            target.write_bytes(data)
        for line in data.decode("utf-8-sig").splitlines():
            if line.startswith("import "):
                pending.extend(name for name in line[7:].split() if name.startswith("ConnesWeilRH"))
    print("MIRROR_CLOSURE_SYNCED", len(copied), flush=True)
    subprocess.run([str(args.lake), "build", "ConnesWeilRH.Dev." + AUDIT], cwd=mirror, check=True)


if __name__ == "__main__":
    main()
