#!/usr/bin/env python3
"""Record 1329 - G8 P1 column-energy antiperiodicity probe (official run).

Implements EXACTLY the preregistration committed at ad0bc70 in
docs/proofs/1329_g8_p1_column_energy_antiperiodicity_probe_preregistration.md.
MODEL-twin numerics only (law 65): makes no claim about the formal
ran P_S or the Lean premise hcolumn.

Registered design (section numbers cite the prereg):
  statistic  E_M(X,p) = sum_j ||(I + U_t) e_j||^2 over an ONB {e_j} of
             ker A (discretized frame-range twin), t = log p;
             on the per-prime torus L_p = 2 log p the shift U_t is the
             exact grid roll by M/2 and Fourier mode n carries
             eigenvalue (-1)^n (antiperiodic modes = odd n).
  models     M0 no constraints (anchor E=2M),
             M1 K=3 generic Gaussian rows (registered seed 1329),
             M2 exclusion of ALL even modes K=M/2 (positive control E=0),
             M3 symmetric resonant-lattice modes {0,+-1,...,+-(K-1)/2},
                K in {3,9,33};
             J1 = M1 at p=2 plus M1 at p=3 (derived report).
  gamma      dyadic exponent log2(E_{2M}/E_M); bands 0.15 / 0.85 (prereg 4)
  gates      G1 unitarity 1e-12; G2 two trace paths 1e-8*max(1,E);
             G3v2 basis-invariance (64 random Givens pair-mixings of the
                null ONB; amendment A2) 1e-8;
             G4 anchors M0 2M, M2 0; G5 shift-sign agreement 1e-8.
             any breach -> ABORTED-UNINFORMATIVE (exit 1 before verdict).
"""
import json
import math
import sys
import time

import numpy as np

PRIMES = [2, 3, 5, 7, 11]
MS = [512, 1024, 2048, 4096]
M3_KS = [3, 9, 33]
SEED = 1329
BAND_CONV = 0.15
BAND_DIV = 0.85
TOL_G1 = 1e-12
TOL_REL = 1e-8


def fourier_rows(mode_ids, M):
    """Orthonormal Fourier-mode evaluation rows for the given mode ids."""
    k = np.arange(M)
    V = np.empty((len(mode_ids), M), dtype=complex)
    for r, n in enumerate(mode_ids):
        V[r] = np.exp(2j * math.pi * (n % M) * k / M) / math.sqrt(M)
    return V


def constraint_rows(model, M, rng):
    if model == "M0":
        return np.zeros((0, M), dtype=complex)
    if model == "M1":
        A = (rng.standard_normal((3, M)) + 1j * rng.standard_normal((3, M))) / math.sqrt(M)
        q, _ = np.linalg.qr(A.conj().T)  # M x 3 orthonormal columns
        return q.conj().T
    if model == "M2":
        return fourier_rows(list(range(0, M, 2)), M)  # exclude all even modes
    if model.startswith("M3"):
        m = (int(model.split("-")[1]) - 1) // 2  # inv1 defect: model[2:] kept the dash
        ids = [0] + [s for n in range(1, m + 1) for s in (n, -n)]
        return fourier_rows(ids, M)
    raise ValueError(model)


def energies(rows, M):
    """All registered readouts for one (model, p, M) cell."""
    K = rows.shape[0]
    if K == 0:
        nullb = np.eye(M, dtype=complex)
    else:
        _, _, vh = np.linalg.svd(rows, full_matrices=True)
        nullb = vh[K:].conj().T  # M x (M-K), orthonormal columns
    N = nullb.conj().T  # (M-K) x M, ONB rows
    E = {}
    for sign, name in ((-1, "plus"), (1, "minus")):  # roll -M/2 = U_{+t} convention
        NP = np.roll(N, sign * (M // 2), axis=1)
        D = N + NP
        E[name] = float(np.sum(np.abs(D) ** 2).real)
    # path 2 of G2: tr(P U) = tr(U) - sum_i <v_i, U v_i>, tr(U) = 0 (roll M/2, M>=2)
    trU_rows = 0.0 + 0j
    for v in rows:
        trU_rows += np.vdot(v, np.roll(v, -M // 2))
    E["path2"] = 2.0 * (M - K) - 2.0 * float(trU_rows.real)
    # G1: unitarity of U (roll) on the basis
    g1 = float(np.max(np.abs(np.linalg.norm(np.roll(N, -(M // 2), axis=1), axis=1) - 1.0)))
    # G3v2 (amendment A2): rebasing by 64 random Givens pair-mixings of the
    # null-space ONB rows (each a 2x2 unitary action; orthonormality
    # preserved; audit semantics and tolerance unchanged from prereg sec 3;
    # the dense (M-K)^2 unitary QR was the invocation-1/2 wall-killer).
    g3 = None
    if 0 < K < M:
        dim = M - K
        N2 = N.copy()
        for _ in range(64):
            i, j = int(rng_global.integers(dim)), int(rng_global.integers(dim))
            if i == j:
                continue
            z = rng_global.standard_normal(2) + 1j * rng_global.standard_normal(2)
            nrm = math.sqrt(float((z.real ** 2 + z.imag ** 2).sum()))
            a, b = z[0] / nrm, z[1] / nrm
            ri, rj = N2[i].copy(), N2[j].copy()
            N2[i] = a * ri + b * rj
            N2[j] = -np.conj(b) * ri + np.conj(a) * rj
        D2 = N2 + np.roll(N2, -(M // 2), axis=1)
        E2 = float(np.sum(np.abs(D2) ** 2).real)
        g3 = abs(E2 - E["plus"])
    # null-basis trace path (G2 companion)
    trU_null = float(np.real(np.vdot(N, np.roll(N, -(M // 2), axis=1))))
    return {"E_plus": E["plus"], "E_minus": E["minus"], "E_path2": E["path2"],
            "trU_null": trU_null, "g1": g1, "g3": g3}


rng_global = np.random.default_rng(SEED)

failures = []
cells = {}
t0 = time.time()
print(f"[1329] models M0/M1/M2/M3(3,9,33) primes {PRIMES} ladder {MS} seed {SEED}", flush=True)

for p in PRIMES:
    logp = math.log(p)
    for model in ["M0", "M1", "M2", "M3-3", "M3-9", "M3-33"]:
        rng = np.random.default_rng(SEED)  # M1 rows identical across cells (fixed functional twin)
        series = []
        for M in MS:
            tc = time.time()
            rows = constraint_rows(model, M, rng)
            r = energies(rows, M)
            dt = time.time() - tc
            K = rows.shape[0]
            # registered-shape guard (inv1 defect class: silently wrong K)
            want_K = {"M0": 0, "M1": 3, "M2": M // 2}.get(
                model, int(model.split("-")[1]) if model.startswith("M3") else None)
            if want_K is not None and K != want_K:
                failures.append(f"KSHAPE {model} p={p} M={M}: K={K} registered={want_K}")
            E = r["E_plus"]
            tol = TOL_REL * max(1.0, abs(E))
            if r["g1"] > TOL_G1:
                failures.append(f"G1 {model} p={p} M={M}: {r['g1']:.2e}")
            if abs(E - r["E_path2"]) > tol or abs(2 * (M - K) + 2 * r["trU_null"] - E) > tol:
                failures.append(f"G2 {model} p={p} M={M}: {abs(E - r['E_path2']):.2e} vs {tol:.2e}")
            if r["g3"] is not None and r["g3"] > tol:
                failures.append(f"G3 {model} p={p} M={M}: {r['g3']:.2e}")
            if abs(r["E_plus"] - r["E_minus"]) > tol:
                failures.append(f"G5 {model} p={p} M={M}: {abs(r['E_plus'] - r['E_minus']):.2e}")
            if model == "M0" and abs(E - 2 * M) > TOL_REL * M:
                failures.append(f"G4-M0 p={p} M={M}: {abs(E - 2 * M):.2e}")
            if model == "M2" and E > 1e-10:
                failures.append(f"G4-M2 p={p} M={M}: {E:.2e}")
            series.append({"M": M, "K": K, "L": 2 * logp, **r})
            print(f"[1329] {model} p={p} M={M:5d} K={K:5d} E_plus={E:.6f} "
                  f"E_path2={r['E_path2']:.6f} g1={r['g1']:.1e} "
                  f"g3={'-' if r['g3'] is None else format(r['g3'], '.1e')} "
                  f"dt={dt:.1f}s", flush=True)
        gam = [None] + [math.log2(s2["E_plus"] / s1["E_plus"]) if s1["E_plus"] > 0
                        else (0.0 if s2["E_plus"] <= 1e-10 else None)
                        for s1, s2 in zip(series, series[1:])]
        cells[f"{model}@p{p}"] = {"series": series, "gamma": gam}

# J1: derived report, M1 at p=2 + M1 at p=3
j1 = []
for i in range(len(MS)):
    e2 = cells["M1@p2"]["series"][i]["E_plus"]
    e3 = cells["M1@p3"]["series"][i]["E_plus"]
    j1.append({"M": MS[i], "E": e2 + e3})
j1_gam = [None] + [math.log2(a["E"] / b["E"]) for b, a in zip(j1, j1[1:])]
cells["J1"] = {"series": j1, "gamma": j1_gam}

print(json.dumps({"gates_failed": failures}, indent=0)[:400], flush=True)
if failures:
    cells["ABORT"] = {"gates_failed": failures, "verdict": "ABORTED-UNINFORMATIVE"}
    print(json.dumps({"verdict": "ABORTED-UNINFORMATIVE", "gates_failed": failures}, indent=1))
    sys.exit(1)

# branch adjudication (prereg section 4): ONLY repo-lineage models M1/M3
# adjudicate; M0/M2 are anchors and controls, never verdict material.
REPO_LINEAGE = ("M1", "M3-3", "M3-9", "M3-33")
adjudicated = {}
convergent_hits = []
for key, c in cells.items():
    if key == "J1" or key.split("@")[0] not in REPO_LINEAGE:
        continue
    g_top = c["gamma"][-1]
    adjudicated[key] = g_top
    if g_top is not None and g_top <= BAND_CONV:
        convergent_hits.append((key, g_top))
divergent_all = all(g is not None and g >= BAND_DIV for g in adjudicated.values())
if convergent_hits:
    verdict = "SOME-MODEL-CONVERGENT"
elif divergent_all:
    verdict = "LINEAR-DIVERGENT"
else:
    verdict = "SUBLINEAR-UNRESOLVED"

out = {"record": 1329, "prereg_commit": "ad0bc70", "seed": SEED,
       "bands": {"conv": BAND_CONV, "div": BAND_DIV},
       "gamma_top_dyadic": adjudicated, "j1_gamma": j1_gam,
       "verdict": verdict, "cells": cells,
       "runtime_s": round(time.time() - t0, 1)}
with open("docs/proofs/1329_probe_results.json", "w") as f:
    json.dump(out, f, indent=1)
print(f"[1329] GAMMAS {json.dumps(adjudicated)}", flush=True)
print(f"[1329] J1     {j1_gam}", flush=True)
print(f"[1329] VERDICT: {verdict}  (runtime {out['runtime_s']} s)", flush=True)
print("[1329] DONE", flush=True)
