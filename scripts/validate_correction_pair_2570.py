"""Validate record 2570: correction-pair regeneration of the cell2700 chain.

Pre-registered checks, in order:
1. TOKEN HYGIENE - no baseCoefficient token survives in any of the seven
   2570 modules (the 2568 row-scope correction must be total).
2. REGENERATION - the composer re-run reproduces all seven modules
   byte-for-byte (deterministic parameter swap).
3. BASE SELF-CHECK - the composer selfcheck mode still reproduces the
   committed base-pair modules byte-for-byte (the derivation chain is the
   committed one, only the pair changed).
4. PILOT AGREEMENT - the module constants agree with the 2569 external
   repricing: the four signed uppers within their quanta, the exact cell
   total inside the module bound, and bound vs pilot bound within 1e-6.
5. BUILD + AXIOM CENSUS (given --log from a tee'd lake build over the
   seven modules): success footer, no errors or sorry, and every
   #print-axioms target resolves with exactly the axiom trio.
6. MIRROR - the full import closure of the seven modules is byte-equal to
   the ext4 build mirror (given --mirror).
"""
from fractions import Fraction as Q
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODULES = [
    "C1RouteACorrectionCoefficientBoxes2570",
    "C1RouteACorrectionCenterNode2570",
    "C1RouteACorrMidpointDerivatives2570",
    "C1RouteACorrMidpointBounds2700Minus2570",
    "C1RouteACorrFirstJetMidpointMinus2570",
    "C1RouteACorrSharedN02700Minus2570",
    "C1RouteACorrSharedN02701Minus2570",
    "C1RouteACorrectionSecondCell2700MinusCorr2570",
]
TRIO = ["propext", "Classical.choice", "Quot.sound"]


def read_module(name):
    return (ROOT / "ConnesWeilRH/Dev" / f"{name}.lean").read_text()


def check_tokens(result):
    residue = {name: read_module(name).count("baseCoefficient") for name in MODULES}
    assert not any(residue.values()), residue
    result.update(token_hygiene="NO_BASE_COEFFICIENT_TOKENS_IN_2570_MODULES")


def check_regeneration(result):
    """Snapshot, re-run the composer, require byte-identical modules."""
    snapshot = {name: (ROOT / "ConnesWeilRH/Dev" / f"{name}.lean").read_bytes()
                for name in MODULES}
    readback = ROOT / "results/2570_generation_readback.json"
    snapshot_rb = readback.read_bytes()
    proc = subprocess.run([sys.executable, str(ROOT / "scripts/generate_correction_pair_2570.py")],
                          capture_output=True, text=True, timeout=1800)
    assert proc.returncode == 0, proc.stdout[-4000:] + proc.stderr[-2000:]
    for name in MODULES:
        assert (ROOT / "ConnesWeilRH/Dev" / f"{name}.lean").read_bytes() == snapshot[name], name
    assert readback.read_bytes() == snapshot_rb, "readback json drift"
    result.update(regeneration="ALL_MODULES_BYTE_IDENTICAL_ON_RERUN")


def check_selfcheck(result):
    proc = subprocess.run(
        [sys.executable, str(ROOT / "scripts/generate_correction_pair_2570.py"), "selfcheck"],
        capture_output=True, text=True, timeout=3600)
    assert proc.returncode == 0, proc.stdout[-4000:] + proc.stderr[-2000:]
    assert "SELFCHECK boxes body byte-equal modulo header" in proc.stdout
    assert "SELFCHECK midpoint/firstjet/shared byte-equal to committed modules" in proc.stdout
    result.update(base_selfcheck="DERIVATION_REPRODUCES_COMMITTED_BASE_MODULES")


def check_pilot(result):
    readback = json.loads((ROOT / "results/2570_generation_readback.json").read_text())
    pilot = json.loads(
        (ROOT / "results/2569_cell2700_minus_correction_repricing.json").read_text())
    exact = pilot["correction_repricing"]["exact"]
    displays = pilot["correction_repricing"]["displays"]
    mid = Q(readback["mid_upper"])
    jet = Q(readback["jet_upper"])
    n0l = Q(readback["n0l_upper"])
    n0r = Q(readback["n0r_upper"])
    # the mid/jet module uppers cover the pilot aggregates (their rounding
    # quanta are 1/10^7 against the pilot's 1/10^8); the endpoint uppers use
    # a different rounding-charge shape than the pilot (the 2542 chain
    # carries the exp error inside its own lemmas), so there the two
    # roundings of the same aggregate must agree within the charge scale.
    assert mid >= Q(exact["mid_upper"]) and jet >= Q(exact["j1_upper"])
    assert all(b - a <= Q(1, 10 ** 7) for a, b in (
        (Q(exact["mid_upper"]), mid), (Q(exact["j1_upper"]), jet)))
    assert all(abs(a - b) <= Q(2, 10 ** 12) for a, b in (
        (Q(exact["n0l_upper"]), n0l), (Q(exact["n0r_upper"]), n0r)))
    bound = Q(readback["cell_bound"])
    pilot_bound = Q(exact["cell_bound"])
    assert bound >= pilot_bound, (str(bound), str(pilot_bound))
    assert bound - pilot_bound < Q(1, 10 ** 6)
    assert abs(float(bound) - displays["piece_sum"]) < 1e-9
    # the assembly's L1 bridge literal is bitwise the pilot aggregate
    assert readback["third_l1_display"] == displays["third_aggregate"]
    result.update(
        pilot_agreement="UPPERS_COVER_AND_MATCH_2569",
        module_bound=str(bound), pilot_bound=str(pilot_bound),
        bound_vs_pilot=float(bound / pilot_bound))


def check_build(result, log_path):
    log = log_path.read_text()
    assert not re.search(r"^error:", log, re.M), "build errors in log"
    assert "declaration uses 'sorry'" not in log, "sorry in build"
    footers = re.findall(r"^Build completed successfully.*$", log, re.M)
    assert footers, "no success footer"
    expected = set()
    for name in MODULES:
        expected.update(re.findall(r"#print axioms ConnesWeilRH\.Dev\.(\w+)",
                                   read_module(name)))
    matches = re.findall(
        r"'ConnesWeilRH\.Dev\.([^\s']+2570)' depends on axioms:\s*\[([^]]*)\]", log)
    audits = {name: [v.strip() for v in ax.split(",") if v.strip()]
              for name, ax in matches}
    assert set(audits) == expected, (expected - set(audits), set(audits) - expected)
    bad = {n: ax for n, ax in audits.items() if ax != TRIO}
    assert not bad, bad
    result.update(build_footer=footers[-1], axiom_audit=dict(
        verdict="AXIOM_TRIO_ALL", count=len(audits), names=sorted(audits)))


def check_mirror(result, mirror):
    pending = ["ConnesWeilRH.lean"] + [
        f"ConnesWeilRH/Dev/{name}.lean" for name in MODULES]
    hashes: dict[str, str] = {}
    while pending:
        rel = pending.pop()
        if rel in hashes:
            continue
        data = (ROOT / rel).read_bytes()
        assert data == (mirror / rel).read_bytes(), rel
        hashes[rel] = hashlib.sha256(data).hexdigest()
        for line in data.decode("utf-8-sig").splitlines():
            if line.startswith("import "):
                pending.extend(m.replace(".", "/") + ".lean"
                               for m in line[7:].split()
                               if m.startswith("ConnesWeilRH"))
    for rel in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        assert (ROOT / rel).read_bytes() == (mirror / rel).read_bytes(), rel
    result.update(mirror_byte_equality="IMPORT_CLOSURE_IDENTICAL",
                  source_sha256=hashes)
    return len(hashes)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path)
    parser.add_argument("--mirror", type=Path)
    args = parser.parse_args()
    result = dict(record=2570,
                  scope=("correction-pair regeneration of the cell2700 minus "
                         "correction-second chain; eight Lean modules; no RH claim"),
                  rh_claim=False)
    check_tokens(result)
    check_regeneration(result)
    check_selfcheck(result)
    check_pilot(result)
    mirror_count = None
    if args.log:
        assert args.mirror, "--log requires --mirror"
        check_build(result, args.log)
        mirror_count = check_mirror(result, args.mirror)
        result["status"] = "CORRECTION_PAIR_REGENERATION_VALIDATED"
    out = ROOT / "results/2570_correction_pair_validation.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "source_sha256"},
                     indent=2))
    if mirror_count is not None:
        print("SOURCE_SHA256_COUNT", mirror_count)


if __name__ == "__main__":
    main()
