#!/usr/bin/env python3
"""One bounded, model-grade comparison on the exact stored row-B owner.

The frozen 2720 evaluator is preserved. A disclosed clone corrects only the
crossing-cell distance. New derivative inputs are proved Lean bounds, but
mpf arithmetic here is diagnostic, not a directed-rounding certificate.
"""

import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import signal
import struct
import sys
import time
import types

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from full_line_envelope_reaudit_2729 import interval_distance, tail_bound

OUT = ROOT / "results/3115_routeb_split_rung_probe.json"
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"
CAPTURE = ROOT / "results/2722f_rowB_capture_data.json"
PINS = {"C4": 61000000., "C2": 29000000., "q": 2.6e-16}


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def rational(text):
    numerator, sep, denominator = text.partition("/")
    return mp.mpf(numerator) / mp.mpf(denominator if sep else "1")


def read_complex(pair):
    return mp.mpc(*(rational(s) for s in pair))


def exact_input_consts(nodes, values):
    """Subtract lifted exact rationals, without binary64 node subtraction.

    Subsequent mpf operations remain rounded; the padding is diagnostic.
    """
    result = []
    for index, (z, value) in enumerate(zip(nodes, values)):
        if value == 0:
            continue
        others = [w for j, w in enumerate(nodes) if j != index]
        denominator = mp.fprod(w - z for w in others)
        result.append({
            "z": z, "im": z.imag,
            "c_abs": abs(value) / (abs(denominator) * 59049)
                     * (1 + mp.mpf("1e-12")),
            "Ez": mp.exp(max(abs(z.real), abs(1 - z.real)))
                  * (1 + mp.mpf("1e-25")),
            "others": [(max(abs(w.real), abs(1 - w.real)), w.imag)
                       for w in others],
        })
    return result


def covered(cells, start, end):
    cursor = start
    for lo, hi in sorted(cells):
        if lo > cursor or hi < lo:
            return False
        cursor = max(cursor, hi)
    return cursor >= end


def attached_tail_bound(constants, power, threshold):
    """Evaluate the actual-cardinal exterior formula of the 3115 Lean theorem.

    This uses the linear polynomial factor ds+T+|Im w|, slightly larger
    than the square-root factor in record 2729, with the same sharp
    separation T-|Im z|. It covers both signs for every |t|>=T.
    """
    total = mp.mpf(0)
    for term in constants:
        if abs(term["im"]) >= threshold:
            raise ValueError("exterior threshold crosses an active node")
        if len(term["others"]) + power > 70:
            raise ValueError("seventh rung cannot dominate this degree")
        polynomial = mp.fprod(ds + threshold + abs(iw) for ds, iw in term["others"])
        arm = term["Ez"] * 2000000000 * 2 ** 7 / (threshold - abs(term["im"])) ** 7
        total += term["c_abs"] * polynomial * arm ** 10 * threshold ** power
    return float(total / (2 * mp.pi) ** power * (1 + mp.mpf("1e-12")))


def main():
    started = time.monotonic()
    checks = {}

    def check(name, value):
        checks[name] = bool(value)
        print(("PASS " if value else "FAIL ") + name, flush=True)
        if not value:
            raise RuntimeError(name)

    # A timeout is a failed run, never permission to preserve an old PASS.
    def expired(_signum, _frame):
        raise TimeoutError("15-minute probe budget exhausted")

    signal.signal(signal.SIGALRM, expired)
    signal.alarm(900)
    reference = json.loads((ROOT / "results/2720_p3_certified_strip_constants.json")
                           .read_text())["rows"][1]["certified"]
    capture = json.loads(CAPTURE.read_text())
    capture_module = ROOT / "ConnesWeilRH/Dev/C1RowBStoredCapture2722F.lean"
    check("capture_matches_lean_source",
          digest(capture_module) == capture["modules"][capture_module.name])
    source = PARENT.read_text(encoding="utf-8")
    spec = importlib.util.spec_from_file_location("legacy3115", PARENT)
    legacy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(legacy)
    needle = 'min(abs(t_lo - cz["im"]), abs(t_hi - cz["im"]))'
    check("single_disclosed_distance_repair", source.count(needle) == 1)
    fixed = types.ModuleType("corrected3115")
    fixed.__file__ = str(PARENT)
    fixed.interval_distance = interval_distance
    exec(compile(source.replace(needle, 'interval_distance(t_lo, t_hi, cz["im"])'),
                 str(PARENT), "exec"), fixed.__dict__)

    check("crossing_and_endpoint_distances", interval_distance(0, 1, .5) == 0
          and interval_distance(0, 1, 1) == 0)
    check("external_distances_both_sides", interval_distance(0, 1, 2) == 1
          and interval_distance(-1, 0, -2) == 1)
    check("coverage_guard_accepts_overlays", covered([(0, 1), (.5, 2)], 0, 2))
    check("coverage_guard_rejects_gap", not covered([(0, 1), (1.01, 2)], 0, 2))

    # Same-run reproduction of the historical evaluator and its own D-table.
    row = legacy.Row_(legacy.CANDIDATES[1])
    old_D, _ = legacy.certified_D_table()
    cb_old = legacy.make_consts(row.base_nodes, [1.] * len(row.base_nodes))
    cc_old = legacy.make_consts(row.owner, row.values)
    control = {"C4": legacy.scan_channel(cb_old, 4, old_D)[1],
               "C2": legacy.scan_channel(cc_old, 2, old_D)[1],
               "q": legacy.q_star_at(cb_old, 64, old_D)}
    for key, field in [("C4", "C4_star"), ("C2", "C2_star_corr"),
                       ("q", "q_star_T64")]:
        check("legacy_bitwise_" + key,
              struct.pack("d", control[key]) == struct.pack("d", reference[field]))

    owner = [read_complex(pair) for pair in capture["owner"]]
    targets = [read_complex(pair) for pair in capture["targets"]]
    values = [read_complex(pair) for pair in capture["values"]]
    check("owner_count_and_distinctness", len(owner) == len(set(owner)) == 56)
    check("target_count_and_distinctness", len(targets) == len(set(targets)) == 8)
    check("target_indices", [owner[i] for i in capture["target_owner_index"]] == targets)
    check("same_frozen_owner", [complex(z) for z in owner] == list(row.owner))
    check("same_frozen_targets", [complex(z) for z in targets] == list(row.base_nodes))
    check("same_frozen_values", [complex(z) for z in values] == list(row.values))
    check("three_active_correction_terms", [i for i, v in enumerate(values) if v != 0]
          == [48, 49, 52])
    check("all_owner_heights_below_exterior_threshold",
          all(abs(z.imag) < fixed.TAIL_T for z in owner))
    check("actual_owner_degrees_fit_seventh_rung",
          len(owner) + 2 <= 71 and len(targets) + 4 <= 71)

    proved = {1: mp.mpf(2), 2: mp.mpf(8), 3: mp.mpf(787283385) / 10000000,
              4: mp.mpf(1500), 7: mp.mpf(2000000000)}
    table = {k: proved.get(k, mp.inf) for k in range(1, 13)}
    cb = exact_input_consts(targets, [mp.mpf(1)] * len(targets))
    cc = exact_input_consts(owner, values)
    for name, constants in [("base", cb), ("correction", cc)]:
        cells, end = fixed.scan_cells([float(c["im"]) for c in constants])
        check(name + "_compact_coverage", covered(cells, 0., end))
        check(name + "_compact_end_below_tail", 0 < end < fixed.TAIL_T)

    finite = {"C4": fixed.scan_channel(cb, 4, table)[1],
              "C2": fixed.scan_channel(cc, 2, table)[1],
              "q": fixed.q_star_at(cb, 64, table)}
    tails, choices, totals, attached = {}, {}, {}, {}
    for key, constants, power in [("C4", cb, 4), ("C2", cc, 2), ("q", cb, 0)]:
        tail, choice = tail_bound(constants, proved, power, mp.mpf(fixed.TAIL_T))
        check(key + "_has_nonpositive_tail_degree", tail is not None)
        tails[key], choices[key] = tail, choice
        attached[key] = attached_tail_bound(constants, power, mp.mpf(fixed.TAIL_T))
        check(key + "_attached_tail_covers_sharper_model", attached[key] >= tail)
        totals[key] = max(finite[key], attached[key])
        check(key + "_model_pin", totals[key] <= PINS[key])

    low = {k: proved[k] for k in (1, 2, 3, 4)}
    rejected, degree = tail_bound(cc, low, 2, mp.mpf(fixed.TAIL_T))
    check("reject_low_rung_full_line_correction", rejected is None
          and degree["unbounded_envelope_degree"] == 17)
    check("empty_owner_tail", tail_bound([], proved, 2, mp.mpf(600))[0] == 0.)
    max_rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
    check("resident_memory_within_budget", max_rss <= 1024 ** 3)
    paths = [Path(__file__), PARENT, CAPTURE, capture_module,
             ROOT / "scripts/full_line_envelope_reaudit_2729.py",
             ROOT / "ConnesWeilRH/Dev/C1RouteBSplitRungEnvelope3115.lean",
             ROOT / "ConnesWeilRH/Dev/C1RouteBCardinalExterior3115.lean",
             ROOT / "ConnesWeilRH/Dev/C1SeedD4D7Certified3103.lean",
             ROOT / "ConnesWeilRH/Dev/C1ExplicitSeedThirdOrderIntervalCertificate.lean"]
    report = {
        "record": 3115, "status": "MODEL-PASS", "checks": checks,
        "legacy": control, "proved_D": {str(k): str(v) for k, v in proved.items()},
        "finite": finite, "two_sided_tail": tails, "tail_choices": choices,
        "attached_cardinal_exterior_tail": attached,
        "global_model_bound": totals, "pins": PINS,
        "relative_slack": {k: 1 - totals[k] / PINS[k] for k in totals},
        "tail_threshold": fixed.TAIL_T, "elapsed_seconds": time.monotonic() - started,
        "max_rss_bytes": max_rss,
        "hash_convention": "SHA-256 of text with CRLF normalized to LF",
        "provenance": {p.relative_to(ROOT).as_posix(): digest(p) for p in paths},
        "scope": "Exact stored dyadic inputs lifted into diagnostic mpf arithmetic; "
                 "both frequency signs and infinite tails. No Lean pin, no "
                 "directed-rounding certificate, no arbitrary-rho transfer, no RH.",
    }
    OUT.write_text(json.dumps(report, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    signal.alarm(0)
    print(json.dumps({k: report[k] for k in ("status", "global_model_bound",
                                           "relative_slack", "elapsed_seconds")}, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        OUT.parent.mkdir(exist_ok=True)
        OUT.write_text(json.dumps({"record": 3115, "status": "FAIL",
                                   "failure_type": type(exc).__name__,
                                   "failure": str(exc)}, indent=2) + "\n", encoding="utf-8")
        print(f"probe failed: {exc}", file=sys.stderr)
        sys.exit(1)
