"""Independent checks for the replay-mechanism gate probe (record 2567).

Pre-registered acceptance semantics: the cbv variant must build with all 30
replay equalities proven on the axiom trio; the decide and rfl variants are
EXPECTED to fail at this interface (build failure is the readback, not a
validator error), each with exactly 30 tactic-error lines naming its tactic.
All three modules' definition payloads are independently replayed through
the 2553 validator machinery after renaming back to the accepted node names,
regeneration is byte-checked, matched timings are parsed from the time -v
output, and a corrupted factor must be rejected.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

from generate_complex_exp_node_2541 import ROOT
from generate_paired_nodes_2553 import CASES
from generate_replay_probe_2567 import TACTICS, render
from validate_boundary_jets_2548 import check
from validate_paired_nodes_2553 import check_node

BUILDS = {"Cbv": True, "Decide": False, "Rfl": False}


def timings(log_text):
    wall = re.search(r"Elapsed \(wall clock\) time.*:\s*([\d:.]+)", log_text)
    user = re.search(r"User time \(seconds\):\s*([\d.]+)", log_text)
    assert wall and user, "time -v output missing"
    parts = [float(v) for v in wall.group(1).split(":")]
    seconds = parts[0] if len(parts) == 1 else 60 * parts[-2] + parts[-1]
    return dict(wall_s=seconds, user_s=float(user.group(1)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror", type=Path, required=True)
    args = parser.parse_args()
    reports, timings_out, hashes, errors_out = {}, {}, {}, {}
    for tactic in TACTICS:
        relative = f"ConnesWeilRH/Dev/C1RouteAReplayProbe{tactic}2567.lean"
        source = (ROOT / relative).read_text(encoding="utf-8")
        assert source == render(tactic), relative
        normalized = re.sub(r"\bprobe" + tactic + r"(\w*)2567\b",
                            lambda m: "edgeN05440Plus" + m[1] + "2548", source)
        assert "probe" not in normalized
        # The Replay-pruned module legitimately drops the sigma-sign text the
        # 2553 header sentinel checks, so replay through check() directly
        # (check_node's sentinel would reject the pruned module header).
        grid, sigma = CASES["N05440Plus"]
        reports[tactic] = check(normalized, "N05440Plus", grid_order=(grid, 3),
                                sigma=sigma)
        log = (args.mirror / f"build-logs/2567_{tactic}.log").read_text(
            encoding="utf-8", errors="replace")
        errors = re.findall(r": error: (Tactic `(\w+)` failed[^\n]*)", log)
        error_count = len(re.findall(r": error:", log))
        audits = re.findall(
            r"'ConnesWeilRH\.Dev\.(probe" + tactic + r"P\d{3}Replay2567)' "
            r"depends on axioms:\s*\[([^]]*)\]", log)
        if BUILDS[tactic]:
            assert error_count == 0, (tactic, error_count)
            assert len(audits) == 30, (tactic, len(audits))
            assert all(ax.split(", ") == ["propext", "Classical.choice", "Quot.sound"]
                       for _, ax in audits), tactic
            axiom_note = "all 30 replay theorems on the axiom trio"
        else:
            assert error_count == 30, (tactic, error_count)
            assert len(errors) == 30 and all(e[1] == tactic.lower() for e in errors), \
                (tactic, [e[1] for e in errors][:3])
            assert any("sorryAx" in ax for _, ax in audits), tactic
            axiom_note = "failed theorems print sorryAx; mechanism unavailable"
        timings_out[tactic] = timings(log)
        errors_out[tactic] = dict(error_count=error_count, note=axiom_note,
                                  built=BUILDS[tactic])
        hashes[relative] = hashlib.sha256((args.mirror / relative).read_bytes()).hexdigest()
    index = reports["Cbv"]["active"][0]
    prefix = f"pairedN05440PlusP{index:03d}"
    base = (ROOT / "ConnesWeilRH/Dev/C1RouteAPairedN05440Plus2553.lean").read_text(encoding="utf-8")
    corrupted = re.sub(r"(def " + prefix + r"Factor2553\b.*?:=).*?(?=\n\n)",
                       lambda m: m[1] + " (0, 0)", base, count=1, flags=re.S)
    assert corrupted != base
    try:
        check(corrupted, "N05440Plus", grid_order=(grid, 3), sigma=sigma)
    except AssertionError:
        factor_rejected = True
    else:
        raise AssertionError("Corrupted factor accepted")
    verdict = ("cbv is the only kernel mechanism closing the compactExp2547 "
               "replay equalities at this interface; the 2566 cost projection "
               "stands and the segment count governs leases")
    result = dict(
        record=2567,
        scope="replay-mechanism gate probe: matched cbv/decide/rfl readings on "
              "the accepted node5440 plus replay; no production generator or "
              "accepted certificate changed",
        gate_verdict=verdict,
        variant_expectations=BUILDS, error_census=errors_out,
        reports=reports, timings=timings_out,
        cbv_reference=dict(wall_s=30.17, user_s=72.27, source="record 2554 replay phase"),
        corrupted_factor_rejected=factor_rejected,
        source_sha256=hashes,
        baseline_log="build-logs/2567_baseline.log",
        full_grid_certificate=False, membership_claim=False, rh_claim=False)
    (ROOT / "results/2567_replay_probe_readback.json").write_text(
        json.dumps(result, indent=2) + "\n")
    for tactic in TACTICS:
        print(f"REPLAY_PROBE_{tactic}", "built" if BUILDS[tactic] else "FAILED",
              timings_out[tactic], flush=True)
    print("REPLAY_PROBE_READBACK_PASS", flush=True)


main()
