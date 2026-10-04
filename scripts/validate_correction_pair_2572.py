"""Validate record 2572: cell2701-minus correction-pair chain.

Pre-registered checks, in order:
1. TOKEN HYGIENE - no baseCoefficient token, no plus-flavored sigma literal,
   no Plus token, and (in the assembly) no cell-2700 token, no 2548 edge-def
   machinery, and the committed 2570 shared module reused as the left
   endpoint.
2. REGENERATION - the composer re-run reproduces the five modules and the
   readback JSON byte-for-byte.
3. BASE SELF-CHECK - the composer selfcheck mode reproduces the committed
   2558 MidpointBounds / 2565 first-jet / 2558 batch-value modules byte for
   byte (the derivation chain is the committed one, only the cell changed).
4. PILOT AGREEMENT - the module constants agree with the 2572 repricing:
   the midpoint/first-jet uppers cover the pilot aggregates within their
   quanta, the endpoint uppers match within the charge scale, the exact cell
   total inside the module bound, and bound vs pilot bound within 1e-6.
5. BUILD + AXIOM CENSUS (given --log from a tee'd lake build over the
   five modules): success footer, no errors or sorry, and every #print-axioms
   target in the five modules resolves with exactly the axiom trio.
6. MIRROR - the full import closure of the five modules is byte-equal to
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

from price_cell2700_minus_2565 import scalar_defs

ROOT = Path(__file__).resolve().parent.parent
MODULES = [
    "C1RouteACorrMidpointDerivatives2701Minus2572",
    "C1RouteACorrMidpointBounds2701Minus2572",
    "C1RouteACorrFirstJetMidpointMinus2572",
    "C1RouteACorrSharedN02702Minus2572",
    "C1RouteACorrectionSecondCell2701MinusCorr2572",
]
N0L_MODULE = "C1RouteACorrSharedN02701Minus2570"
AUDIT_MODULES = MODULES + [
    "C1RouteACorrectionTwoCellSegment2572",
    "C1RouteACorrectionTwoCellSegment2572Audit",
]
TRIO = ["propext", "Classical.choice", "Quot.sound"]


def read_module(name):
    return (ROOT / "ConnesWeilRH/Dev" / f"{name}.lean").read_text()


def check_tokens(result):
    for name in MODULES:
        text = read_module(name)
        assert "baseCoefficient" not in text, name
        assert "Plus" not in text, name
        # sigma must stay minus: no bare plus-half literal (grid halves like
        # (5403 : ℝ) / 2 carry the record tag, so the bare spellings are
        # unambiguous sigma markers)
        for plus_form in ("(1/2)", "(1 / 2", "(+1/2)"):
            assert plus_form not in text, (name, plus_form)
    asm = read_module(MODULES[-1])
    assert asm.count("noncomputable def corrThirdAggregate2572 : ℝ :=") == 1
    assembly_body = asm[asm.index("namespace ConnesWeilRH.Dev"):]
    for banned in ("edgeLeft", "edgeRight", "edgeMidpoint", "2548",
                   "C02700", "2700Minus", "(2700 : ℝ)", "(5401 : ℝ)"):
        assert banned not in assembly_body, (MODULES[-1], banned)
    assert f"import ConnesWeilRH.Dev.{N0L_MODULE}" in asm, "n0l reuse missing"
    assert "kernelN02701MinusPosition2555" in asm and \
        "batchN02702MinusPosition2558" in asm, "endpoint positions missing"
    result.update(token_hygiene="NO_BASE_PLUS_2700_OR_EDGE_TOKENS_IN_2572_MODULES",
                  n0l_reuse=N0L_MODULE)


def check_regeneration(result):
    snapshot = {name: (ROOT / "ConnesWeilRH/Dev" / f"{name}.lean").read_bytes()
                for name in MODULES}
    readback = ROOT / "results/2572_generation_readback.json"
    snapshot_rb = readback.read_bytes()
    proc = subprocess.run([sys.executable, str(ROOT / "scripts/generate_correction_pair_2572.py")],
                          capture_output=True, text=True, timeout=1800)
    assert proc.returncode == 0, proc.stdout[-4000:] + proc.stderr[-2000:]
    for name in MODULES:
        assert (ROOT / "ConnesWeilRH/Dev" / f"{name}.lean").read_bytes() == snapshot[name], name
    assert readback.read_bytes() == snapshot_rb, "readback json drift"
    result.update(regeneration="ALL_MODULES_BYTE_IDENTICAL_ON_RERUN")


def check_selfcheck(result):
    proc = subprocess.run(
        [sys.executable, str(ROOT / "scripts/generate_correction_pair_2572.py"), "selfcheck"],
        capture_output=True, text=True, timeout=3600)
    assert proc.returncode == 0, proc.stdout[-4000:] + proc.stderr[-2000:]
    assert "SELFCHECK midpoint/firstjet/shared2702 byte-equal to committed modules" \
        in proc.stdout
    result.update(base_selfcheck="DERIVATION_REPRODUCES_COMMITTED_BASE_MINUS_MODULES")


def check_pilot(result):
    readback = json.loads((ROOT / "results/2572_generation_readback.json").read_text())
    pilot = json.loads(
        (ROOT / "results/2572_cell2701_minus_correction_repricing.json").read_text())
    exact = pilot["correction_repricing"]["exact"]
    displays = pilot["correction_repricing"]["displays"]
    mid = Q(readback["mid_upper"])
    jet = Q(readback["jet_upper"])
    n0l = Q(readback["n0l_upper"])
    n0r = Q(readback["n0r_upper"])
    # the mid/jet module uppers cover the pilot aggregates within their
    # rounding quanta; the endpoint uppers use a different rounding-charge
    # shape than the pilot, so the two roundings of the same aggregate must
    # agree within the charge scale
    assert mid >= Q(exact["mid_upper"]) and jet >= Q(exact["j1_upper"])
    assert all(b - a <= Q(1, 10 ** 7) for a, b in (
        (Q(exact["mid_upper"]), mid), (Q(exact["j1_upper"]), jet)))
    assert all(abs(a - b) <= Q(2, 10 ** 12) for a, b in (
        (Q(exact["n0l_upper"]), n0l), (Q(exact["n0r_upper"]), n0r)))
    # the reused left endpoint must be bitwise the committed 2570 scalar
    committed_n0l = Q(json.loads(
        (ROOT / "results/2570_generation_readback.json").read_text())["n0r_upper"])
    assert n0l == committed_n0l, (str(n0l), str(committed_n0l))
    bound = Q(readback["cell_bound"])
    pilot_bound = Q(exact["cell_bound"])
    assert bound >= pilot_bound, (str(bound), str(pilot_bound))
    assert bound - pilot_bound < Q(1, 10 ** 6)
    assert abs(float(bound) - displays["piece_sum"]) < 1e-9
    # the assembly's L1 bridge literal is bitwise the pilot aggregate
    assert readback["third_l1_display"] == displays["third_aggregate"]
    result.update(
        pilot_agreement="UPPERS_COVER_AND_MATCH_2572_REPRICING",
        module_bound=str(bound), pilot_bound=str(pilot_bound),
        bound_vs_pilot=float(bound / pilot_bound),
        n0l_bitwise_committed_2570=True)


def check_build(result, log_path):
    log = log_path.read_text()
    assert not re.search(r"^error:", log, re.M), "build errors in log"
    assert "declaration uses 'sorry'" not in log, "sorry in build"
    footers = re.findall(r"^Build completed successfully.*$", log, re.M)
    assert footers, "no success footer"
    expected = set()
    for name in AUDIT_MODULES:
        expected.update(re.findall(r"#print axioms ConnesWeilRH\.Dev\.(\w+)",
                                   read_module(name)))
    audits = {}
    for name, ax in re.findall(
            r"'ConnesWeilRH\.Dev\.([^\s']+)' depends on axioms:\s*\[([^]]*)\]", log):
        audits[name] = [v.strip() for v in ax.split(",") if v.strip()]
    missing = expected - set(audits)
    assert not missing, missing
    bad = {n: audits[n] for n in expected if audits[n] != TRIO}
    assert not bad, bad
    result.update(build_footer=footers[-1], axiom_audit=dict(
        verdict="AXIOM_TRIO_ALL", count=len(expected), names=sorted(expected)))


def check_mirror(result, mirror):
    pending = ["ConnesWeilRH.lean"] + [
        f"ConnesWeilRH/Dev/{name}.lean" for name in AUDIT_MODULES]
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


def check_exact_segment(result):
    prior = json.loads((ROOT / "results/2570_generation_readback.json").read_text())
    current = json.loads((ROOT / "results/2572_generation_readback.json").read_text())
    assembly = scalar_defs(read_module(MODULES[-1]),
                           r"corrThirdL1Upper2572|corrSecondCell2701MinusUpper2572")
    assert assembly["corrThirdL1Upper2572"] == Q(current["third_l1_sum"])
    assert assembly["corrSecondCell2701MinusUpper2572"] == Q(current["cell_bound"])
    step = 2 * Q(65536001, 10 ** 7) / 10240
    sigma = Q(-1, 2)
    totals = []
    for readback in (prior, current):
        curvature = Q(readback["mid_upper"]) + Q(readback["third_l1_sum"]) * step / 2
        first_jet = Q(readback["jet_upper"])
        endpoints = Q(readback["n0l_upper"]) + Q(readback["n0r_upper"])
        direct = (step * curvature + 2 * abs(sigma) * step *
                  (first_jet + curvature * step / 2) + sigma ** 2 *
                  (step / 2 * endpoints + curvature * step ** 3 / 12))
        affine = ((step + abs(sigma) * step ** 2 + sigma ** 2 * step ** 3 / 12) *
                  curvature + 2 * abs(sigma) * step * first_jet +
                  sigma ** 2 * step / 2 * endpoints)
        assert direct == affine and direct <= Q(readback["cell_bound"])
        totals.append(direct)
    segment_bound = Q(66626849459, 10 ** 12)
    assert segment_bound == Q(prior["cell_bound"]) + Q(current["cell_bound"])
    assert sum(totals) <= segment_bound
    result.update(exact_affine_identity=True, segment_bound=str(segment_bound),
                  segment_total=str(sum(totals)), full_grid_coverage=False,
                  coefficient_membership=False, producer_go=False)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path)
    parser.add_argument("--mirror", type=Path)
    args = parser.parse_args()
    result = dict(record=2572,
                  scope=("cell2701-minus correction-second chain at the correction "
                         "pair: five modules over the reused 2570 boxes/center and "
                         "the reused 2570 shared endpoint at position 2701; the "
                         "first cell-index generalization of the composer; no RH "
                         "claim"),
                  rh_claim=False)
    check_tokens(result)
    check_regeneration(result)
    check_selfcheck(result)
    check_pilot(result)
    check_exact_segment(result)
    mirror_count = None
    if args.log:
        assert args.mirror, "--log requires --mirror"
        check_build(result, args.log)
        mirror_count = check_mirror(result, args.mirror)
        result["status"] = "CORRECTION_PAIR_2701_VALIDATED"
    out = ROOT / "results/2572_correction_pair_validation.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "source_sha256"},
                     indent=2))
    if mirror_count is not None:
        print("SOURCE_SHA256_COUNT", mirror_count)


if __name__ == "__main__":
    main()
