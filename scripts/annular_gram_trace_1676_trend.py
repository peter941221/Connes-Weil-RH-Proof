#!/usr/bin/env python3
"""Meet-dimension EXCESS trend rig (record 1676; F60-permitted quantity).

F60 (record 1675): on a truncated grid the meet dim(E meet Q) >= dimE+dimQ-M
is FORCED for every involutive unitary conjugation, so absolute carrier
readings are void.  The admissible quantities are TREND quantities measured
against the forced count.  This rig measures exactly one such quantity:

    excess(phase, M) = accepted_dim(block of size forced+headroom) - forced,

where `forced` is the EXACT lattice count dimE + dimQ - M (not the float
formula int(2a/du), which rounds 102.4 down to 102 while the true lattice
count at M = 4096 is 103; noted as an erratum-grade correction to the 1675
reference value — the dim-40 readings there are unaffected since 40 < 102).

Calibration by hand (law F27/F28, before running):
  m = 1 (reflection): masks E = {u >= -1}, Q = {u <= 1} meet on the closed
  lattice interval [k1, k2]; at lambda = e^-1 no grid point hits +-1, so the
  model meet EQUALS the forced count: excess_model = 0 predicted.
  Generic random involutive phase: sits at generic position: excess = 0.
Question: does the committed scattering phase carry a stable nonzero excess
(a continuum-meet footprint at grid scale), or does it read like the generic
random control (excess 0)?  A stable excess_separating real from random
across M would be a genuine trend signal; identical excesses re-confirm F60.

Secondary reading: the spectral tail just past the forced count,
ev[forced : forced+8] (defect rates), real vs random.
"""

import json
import math
import sys

import numpy as np

sys.path.insert(0, "scripts")

import annular_gram_trace_1675 as base  # noqa: E402

LAM = float(np.exp(-1.0))
A = 1.0


def exact_lattice_counts(M):
    """E = {k: U_k >= -a}, Q = {k: U_k <= a} on U_k = -L + du*k."""
    du = 2.0 * 40.0 / M
    k1 = math.ceil((40.0 - A) / du - 1e-9)
    k2 = math.floor((40.0 + A) / du + 1e-9)
    dim_e = M - k1
    dim_q = k2 + 1
    return {"du": du, "k1": k1, "k2": k2, "dimE": dim_e, "dimQ": dim_q,
            "forced": dim_e + dim_q - M, "model_meet": k2 - k1 + 1}


def random_involutive_phase(M, seed):
    """Generic unit-modulus phase with the two self-conjugate modes pinned."""
    rng = np.random.default_rng(seed)
    ph = np.exp(2j * np.pi * rng.random(M))
    ph[0] = 1.0
    ph[M // 2] = 1.0
    return ph


def run_grid(M, iters, headroom=60):
    base.rebuild_grid(40.0, M)
    counts = exact_lattice_counts(M)
    forced = counts["forced"]
    dim_block = forced + headroom
    out = {"M": M, "du": counts["du"], "dimE": counts["dimE"],
           "dimQ": counts["dimQ"], "forced_exact": forced,
           "block_dim": dim_block, "iters": iters}
    phases = [
        ("model", np.ones(M, dtype=complex)),
        ("real", base.make_phase()),
        ("random", random_involutive_phase(M, 929 + M)),
    ]
    for name, ph in phases:
        _V, ev, hist = base.meet_block(LAM, ph, dim=dim_block,
                                       iters=iters, seed=777)
        accepted = int(np.sum(ev >= 1.0 - 1e-8))
        accepted_loose = int(np.sum(ev >= 1.0 - 1e-6))
        out[f"{name}_accepted"] = accepted
        out[f"{name}_accepted_tol1e6"] = accepted_loose
        out[f"{name}_excess"] = accepted - forced
        out[f"{name}_sigma_top"] = round(float(np.sqrt(ev[0])), 10)
        out[f"{name}_sigma_at_forced"] = round(float(np.sqrt(ev[forced])), 10)
        out[f"{name}_tail_past_forced"] = [
            round(float(x), 10) for x in ev[forced:forced + 8]]
        out[f"{name}_drift_last100"] = round(
            float(abs(hist[-1][1] - hist[max(0, len(hist) - 3)][1])), 12)
        print(f"[M={M} {name}] accepted={accepted} excess={accepted - forced}"
              f" sigma_top={out[f'{name}_sigma_top']}"
              f" sigma_at_forced={out[f'{name}_sigma_at_forced']}"
              f" tail[0:4]={out[f'{name}_tail_past_forced'][:4]}"
              f" drift={out[f'{name}_drift_last100']}")
    return out


def main():
    allout = {"lambda": LAM, "a": A, "grids": []}
    allout["grids"].append(run_grid(4096, iters=500))
    allout["grids"].append(run_grid(8192, iters=250))

    verdict = []
    for g in allout["grids"]:
        row = {"M": g["M"],
               "forced": g["forced_exact"],
               "excess_model": g["model_excess"],
               "excess_real": g["real_excess"],
               "excess_random": g["random_excess"]}
        verdict.append(row)
        print("[verdict]", json.dumps(row))
    allout["verdict"] = verdict

    with open("annular_gram_trace_1676_trend_results.json", "w") as fh:
        json.dump(allout, fh, indent=1, default=float)
    print("[done] results written to annular_gram_trace_1676_trend_results.json")


if __name__ == "__main__":
    main()
