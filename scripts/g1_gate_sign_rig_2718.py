#!/usr/bin/env python3
"""Record 2718 (G1 swing 2b): model-grade P5 gate SIGN RIG at n = 3.

Task card (bounded-progress gate):
  consumer   riemannHypothesis_of_four_point_span_contradiction_producer,
             via the record-2708 contract P5 duty at n = 3 -- the named
             map-103 reopen probe (sharpened by records 2716/2717)
  owner      the STORED record-1980 trial-owner models at
             (gamma_1, N=4, n=3) and (gamma_2, N=5, n=3); node constants
             are the stored floats, taken as the owner definition
  premise    the gate-branch signs (C < 0; sign(det)) at the candidate
             rows are supported only by sampled floats + two-grid agreement
  criterion  per sign claim: margin |C| (resp. |det|) against a total
             allowance = (certified non-seed classes) + A * E_L, where the
             seed-quadrature class E_L is a NAMED premise set to 10x the
             observed 600-vs-1200 Gauss-Legendre spread at the rig's own
             evaluation points; report the critical E_L per claim
  budget     one shadow-rig run, both candidates, primary grid dxi = 0.02;
             seed three-order study at the same evaluation points
  stop       verdict recorded; a bitwise-anchor failure triggers
             environment diagnosis (record-2j/2661 law), never patching
             of committed producer modules

Method (forward-error shadow, record-2249 law): the exact record-2032
pipeline is rebuilt bitwise from the committed modules, then every error
class is certified separately and propagated LINEARLY to the claims:

  R_sigma   float sigma_vec vs an mpmath dps-35 digamma reference --
            EXACT per-node deltas (kills the series-truncation question)
  R_cos     prime-kernel cos/argument rounding, analytic per-term bound
            (|da| <= 4U|a| + 1 ulp on |a| <= 2*pi*25*10, plus np.cos ulp)
            summed with the |w_k| sieve weights (bound 1e-12 * wsum)
  R_trap    trapezoid accumulation: 16U * trapz(|integrand|)
  R_float   cardinal/power roundoff: generous 1e-11 * trapz scale
  E_seed    seed-quadrature premise: |dL| <= E_L uniform at every
            evaluation point; propagates through the cardinal terms
            |dterm_j| <= |c_j||Q_j| E_L (1 + |L(u_j)|/|L(0)|) into
            |dW| <= E_L * G, G = 8|lb|^7|lc|^2 S_b + 2|lb|^8 |lc| S_c,
            then channel-wise A_i = trapz((|sig|+|kp|) |P|^i G) and
            det-wise A_det = |D|A_0 + |C|A_2 + 2|b|A_1 (worst-case
            correlation across channels)
  M_grid    trapezoid discretization premise (T_h vs the continuum
            functional): 10x the observed 0.02-vs-0.01 per-channel
            movement, propagated to the claims with the same weights;
            analytic Euler-Maclaurin remainder deferred (named)

Certified object: the pipeline AS CODE on the stored float node constants
(model grade).  Not certified here: the complete owner (G2), the decay
constants C4/C2 (P3/G4), the shell identification (P4), map-103 reopening,
producer GO, SourceRH, RH.

Run under WSL python3 (the record-2032 artifact era is a WSL-python
product; the record-2j law forbids cross-environment bitwise claims).
"""
from __future__ import annotations

import hashlib
import json
import math
import sys
import time
from pathlib import Path

import numpy as np
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as op      # noqa: E402
import fourpoint_coupling_scan_2028 as scan   # noqa: E402
import fourpoint_diagonal_sign_1918 as rig    # noqa: E402
import fourpoint_owner_density_1959 as legacy  # noqa: E402
import fourpoint_powered_seed_1981 as powered  # noqa: E402
import g1_joint_acceptance_repricing_2716 as r16  # noqa: E402

SRC32 = ROOT / "results/2032_gate_row_search.json"
DXI_PRIMARY = 0.02
DXI_FINE = 0.01
XI_MAX = 25.0
SEED_ORDER = 300
SEED_ORDERS_STUDY = (600, 1200)
U = 2.0 ** -53
CANDIDATES = [(14.134725141734693, 4), (21.022039638771556, 5)]
E_SEED_INFLATION = 10.0
GRID_INFLATION = 10.0
SEED0_EXACT = 59049.0          # laplaceAt(smoothSeed, 0) = 3 exactly -> 3^10
T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


def grid_of(dxi):
    return np.arange(-XI_MAX, XI_MAX + 0.5 * dxi, dxi)


def rebuild_row(rho, N, n, dxi, seed_transform, seed0):
    """The record-2032 call order, verbatim, for one (rho, N, n, dxi)."""
    owner, targets, radius, known = op.build_owner(rho, N)
    values = [op.target_value(rho, z) for z in owner]
    xi = grid_of(dxi)
    centered_orbit = [z - 0.5 for z in op.healthy_targets(rho)[:4]]
    P = np.real(legacy.P_from_nodes(xi, centered_orbit))
    W = scan.build_density(xi, seed_transform, seed0, owner, targets,
                           values, n)
    axis = 0.5 - 2j * math.pi * xi
    lb = op.cardinal_transform(targets, [1.0 + 0j] * len(targets), seed0,
                               axis, seed_transform)
    lc = op.cardinal_transform(owner, values, seed0, axis, seed_transform)
    W_direct = np.abs(lb) ** (2 * (n + 1)) * np.abs(lc) ** 2
    vals, logs = scan.fast_prime_powers_up_to(math.exp(2.0 * (n + 2)))
    kp = scan.direct_prime_channel(xi, vals, logs)
    sig = rig.sigma_vec(2.0 * math.pi * xi)
    fs = (W, P * W, P * P * W)
    arch = [float(np.trapezoid(sig * f, xi)) for f in fs]
    pr = [float(np.trapezoid(kp * f, xi)) for f in fs]
    C = arch[0] + pr[0]
    b = arch[1] + pr[1]
    D = arch[2] + pr[2]
    det = C * D - b * b
    lam = (b / C) if C else float("nan")
    return {
        "xi": xi, "P": P, "W": W, "W_direct": W_direct, "lb": lb, "lc": lc,
        "owner": owner, "targets": targets, "radius": radius,
        "known_count": len(known), "kp": kp, "prime_count": int(vals.size),
        "vals": vals, "logs": logs, "sig": sig,
        "gate": {"arch": arch, "pr": pr, "C": C, "b": b, "D": D, "det": det,
                 "lambda": lam},
    }


def sigma_reference(xi):
    """mpmath digamma reference at dps 35 -> exact per-node sigma."""
    with mp.workdps(35):
        out = np.empty(xi.size, dtype=float)
        for i, x in enumerate(xi):
            z = mp.mpc(0.25, -0.5 * (2.0 * math.pi * float(x)))
            out[i] = float(mp.log(mp.pi) - mp.re(mp.digamma(z)))
    return out


def cardinal_sensitivity(nodes, values, seed0, xi, seed_transform):
    """S(s): |dlb(s)| <= E_L * S(s) under a uniform seed error E_L.

    term_j(s) = c_j Q_j(s) L(s - z_j),  c_j = v_j / (D_j L(0)),
    |dterm_j| <= |c_j| |Q_j| E_L (1 + |L(u_j)| / |L(0)|).
    Zero-valued owner nodes are skipped exactly as in the producer.
    """
    s_axis = 0.5 - 2j * math.pi * xi
    S = np.zeros(xi.size, dtype=float)
    detail = []
    for z, v in zip(nodes, values):
        if abs(v) == 0:
            continue
        denom = op.node_product(nodes, z, z) * seed0
        c = v / denom
        Q = op.node_product(nodes, z, s_axis)
        L = seed_transform(s_axis - z)
        S += np.abs(c) * np.abs(Q) * (1.0 + np.abs(L) / abs(seed0))
        detail.append({"z": [float(z.real), float(z.imag)],
                       "abs_c": float(abs(c)),
                       "max_abs_Q": float(np.max(np.abs(Q))),
                       "max_abs_L": float(np.max(np.abs(L)))})
    return S, detail


def main() -> None:
    d32 = json.loads(SRC32.read_text())
    idx32 = {(r["gamma"], r["N"], r["n"]): r for r in d32["rows"]}

    seed_transform = powered.make_powered_seed(order=SEED_ORDER)
    seed0 = complex(seed_transform(np.array([0j]))[0])

    # ------------------------------------------------ anchor a3: seed0 ---
    d81 = json.loads(
        (ROOT / "results/1981_powered_seed_underapprox.json").read_text())
    s0_ref = d81["seed"]["laplace_at_zero"]
    assert [seed0.real, seed0.imag] == s0_ref, (seed0, s0_ref)
    log("anchor a3 OK: seed0 bitwise == committed 1981 laplace_at_zero")
    a4 = abs(seed0 - SEED0_EXACT)
    log("anchor a4: |L300(0) - 3^10| = %.4e (exact-value corroboration "
        "of the seed-error scale)" % a4)

    results = []
    for gamma, N in CANDIDATES:
        rho = complex(0.55, gamma)
        row32 = idx32[(gamma, N, 3)]
        blk = {"gamma": gamma, "N": N, "n": 3,
               "owner_cardinality": row32["owner_cardinality"],
               "known_zero_count": row32["known_zero_count"],
               "radius": row32["radius"]}

        # --------------------------------------- anchor a1: bitwise row ---
        bad = []
        rebuild = {}
        for dxi, tag in ((DXI_PRIMARY, "dxi0.02"), (DXI_FINE, "dxi0.01")):
            d = rebuild_row(rho, N, 3, dxi, seed_transform, seed0)
            rebuild[tag] = d
            ref = row32[tag]
            g = d["gate"]
            for name, got, want in (("C", g["C"], ref["C"]),
                                    ("b", g["b"], ref["b"]),
                                    ("D", g["D"], ref["D"]),
                                    ("det", g["det"], ref["det"]),
                                    ("lambda", g["lambda"], ref["lambda"]),
                                    ("arch0", g["arch"][0], ref["arch"][0]),
                                    ("arch1", g["arch"][1], ref["arch"][1]),
                                    ("arch2", g["arch"][2], ref["arch"][2])):
                if got != want:
                    bad.append((tag, name, got, want))
        blk["anchor_bitwise_mismatches"] = len(bad)
        if bad:
            blk["anchor_detail"] = [list(x) for x in bad[:12]]
            log("ANCHOR FAIL at (%g, %d): %d mismatches, e.g. %s"
                % (gamma, N, len(bad), bad[0]))
            results.append(blk)
            continue          # environment diagnosis; do not certify
        log("anchor a1 OK: (%g, N=%d) bitwise vs stored rows, both grids"
            % (gamma, N))

        # --------------------------------------------- shadow rig (.02) ---
        d = rebuild["dxi0.02"]
        xi, W, P, kp, sig = d["xi"], d["W"], d["P"], d["kp"], d["sig"]
        lb, lc = d["lb"], d["lc"]
        assert float(np.max(np.abs(W - d["W_direct"]))) == 0.0, "W identity"
        gate = d["gate"]
        C, b, D, det = gate["C"], gate["b"], gate["D"], gate["det"]

        sig_ref = sigma_reference(xi)
        dsig_abs = np.abs(sig - sig_ref)
        log("sigma deltas: max |float - mp35| = %.3e" % dsig_abs.max())

        wsum = float(np.sum(2.0 * d["logs"] / np.sqrt(d["vals"].astype(float))))

        Sb, det_b = cardinal_sensitivity(
            d["targets"], [1.0 + 0j] * len(d["targets"]), seed0, xi,
            seed_transform)
        Sc, det_c = cardinal_sensitivity(
            d["owner"], [op.target_value(rho, z) for z in d["owner"]],
            seed0, xi, seed_transform)
        G = (8.0 * np.abs(lb) ** 7 * np.abs(lc) ** 2 * Sb
             + 2.0 * np.abs(lb) ** 8 * np.abs(lc) * Sc)

        # ------------------------------- channel allowance ledger --------
        wvec = (np.ones_like(P), np.abs(P), P * P)
        g_abs = np.abs(sig) + np.abs(kp)
        chan = []
        for wv in wvec:
            fi = wv * W
            A_seed = float(np.trapezoid(g_abs * wv * G, xi))
            R_sigma = float(np.trapezoid(dsig_abs * wv * W, xi))
            R_sigfl = float(np.trapezoid(4.0 * U * np.abs(sig) * wv * W, xi))
            R_trap_a = 16.0 * U * float(np.trapezoid(np.abs(sig * fi), xi))
            R_cos = 1e-12 * wsum * float(np.trapezoid(fi, xi))
            R_trap_p = 16.0 * U * float(np.trapezoid(np.abs(kp * fi), xi))
            R_float = 1e-11 * float(np.trapezoid(g_abs * fi, xi))
            chan.append({
                "A_seed": A_seed,
                "nonseed": R_sigma + R_sigfl + R_trap_a + R_cos
                           + R_trap_p + R_float,
                "parts": {"R_sigma": R_sigma, "R_sigfl": R_sigfl,
                          "R_trap_arch": R_trap_a, "R_cos": R_cos,
                          "R_trap_pr": R_trap_p, "R_float": R_float},
            })

        # det propagation (worst-case channel correlation)
        A_det = (abs(D) * chan[0]["A_seed"] + abs(C) * chan[2]["A_seed"]
                 + 2.0 * abs(b) * chan[1]["A_seed"])
        ns_det = (abs(D) * chan[0]["nonseed"] + abs(C) * chan[2]["nonseed"]
                  + 2.0 * abs(b) * chan[1]["nonseed"]
                  + 6.0 * U * abs(C * D))
        chan_det = {"A_seed": A_det, "nonseed": ns_det}

        # --------------------------------- seed three-order study --------
        s_axis = 0.5 - 2j * math.pi * xi
        pts = [s_axis - z for z in d["targets"]]
        pts += [s_axis - z for z, v in
                zip(d["owner"], [op.target_value(rho, z)
                                 for z in d["owner"]]) if abs(v) != 0]
        Ls = {SEED_ORDER: seed_transform}
        for o in SEED_ORDERS_STUDY:
            Ls[o] = powered.make_powered_seed(order=o)
        spread = {}
        for o in SEED_ORDERS_STUDY:
            m = 0.0
            for p in pts:
                m = max(m, float(np.max(np.abs(Ls[o](p) - Ls[300](p)))))
            m0 = abs(complex(Ls[o](np.array([0j]))[0]) - seed0)
            spread[str(o)] = {"max_abs_diff_vs_300": m, "abs_diff_at_0": m0}
            log("seed order %d vs 300: max|dL| = %.3e (at 0: %.3e)"
                % (o, m, m0))
        E_obs = spread[str(SEED_ORDERS_STUDY[-1])]["max_abs_diff_vs_300"]
        E_seed = E_SEED_INFLATION * E_obs

        # grid-movement premise: |continuum - T_0.02| charged as 10x the
        # observed 0.02-vs-0.01 per-channel movement (same named-premise
        # class as E_seed; analytic EM remainder deferred)
        gF = rebuild["dxi0.01"]["gate"]
        d_arch = [abs(gate["arch"][i] - gF["arch"][i]) for i in range(3)]
        d_pr = [abs(gate["pr"][i] - gF["pr"][i]) for i in range(3)]
        M_ch = [GRID_INFLATION * (d_arch[i] + d_pr[i]) for i in range(3)]
        M_det = (abs(D) * M_ch[0] + abs(C) * M_ch[2]
                 + 2.0 * abs(b) * M_ch[1])

        # ------------------------------------------------ claims ----------
        claims = []
        for name, margin, ch, mv in (("C_negative", abs(C), chan[0], M_ch[0]),
                                     ("det_sign", abs(det), chan_det,
                                      M_det)):
            total = ch["nonseed"] + ch["A_seed"] * E_seed + mv
            slack = margin - total
            e_crit = ((margin - ch["nonseed"] - mv) / ch["A_seed"]
                      if ch["A_seed"] > 0 else None)
            claims.append({
                "claim": name, "value": margin,
                "nonseed_allowance": ch["nonseed"],
                "A_seed": ch["A_seed"],
                "E_seed_premise": E_seed,
                "grid_movement_premise": mv,
                "total_allowance_at_premise": total,
                "slack_at_premise": slack,
                "E_L_critical": (float(e_crit) if e_crit is not None
                                 else None),
                "ratio_Ecrit_over_Eobs": (float(e_crit / E_obs)
                                          if e_crit is not None and E_obs > 0
                                          else None),
                "GREEN_at_premise": bool(slack > 0),
            })

        # -------------------------- branch robustness at the premise -----
        kind_c, _ = r16.gate_branches(C, b, det)
        dC = chan[0]["nonseed"] + chan[0]["A_seed"] * E_seed + M_ch[0]
        db = chan[1]["nonseed"] + chan[1]["A_seed"] * E_seed + M_ch[1]
        ddet = (chan_det["nonseed"] + chan_det["A_seed"] * E_seed
                + M_det)
        branch_set = set()
        lplus = []
        for sc in (-1, 1):
            for sb in (-1, 1):
                for sd in (-1, 1):
                    kind, gd = r16.gate_branches(C + sc * dC, b + sb * db,
                                                 det + sd * ddet)
                    branch_set.add(kind)
                    if "Lplus" in gd:
                        lplus.append(float(gd["Lplus"]))
        blk.update({
            "sigma_max_delta": float(dsig_abs.max()),
            "prime_weight_sum": wsum,
            "seed_terms_base": det_b, "seed_terms_corr": det_c,
            "G_max": float(np.max(G)),
            "channels": chan, "channel_det": chan_det,
            "seed_study": spread,
            "E_seed_obs": E_obs, "E_seed_premise": E_seed,
            "seed0_exact_gap": a4,
            "seed0_gap_within_Eobs": bool(a4 <= E_obs),
            "grid_movement_channels": M_ch, "grid_movement_det": M_det,
            "claims": claims,
            "branch_center": kind_c,
            "branch_corner_set": sorted(branch_set),
            "branch_robust": bool(branch_set == {kind_c}),
            "Lplus_corner_range": ([min(lplus), max(lplus)]
                                   if lplus else None),
            "gate": gate,
            "masses": {
                "trapz_abs_W": float(np.trapezoid(W, xi)),
                "peak_W": float(np.max(W)),
                "peak_xi": float(xi[int(np.argmax(W))]),
                "trapz_abs_gW": float(np.trapezoid(g_abs * W, xi)),
            },
        })
        results.append(blk)
        log("(%g, N=%d): claims %s | branch %s corners %s"
            % (gamma, N,
               [(c["claim"], c["GREEN_at_premise"],
                 "%.3g" % (c["ratio_Ecrit_over_Eobs"] or 0))
                for c in claims],
               kind_c, sorted(branch_set)))

    out = {
        "record": 2718,
        "title": "G1 swing 2b: model-grade P5 gate sign rig at n = 3 "
                 "(forward-error shadow, named seed premise)",
        "scope": "stored record-1980 trial-owner models; sign claims only; "
                 "NO complete-owner claim, no map-103 reopening, no GO",
        "inputs": {
            "source_2032": "results/2032_gate_row_search.json",
            "source_2032_sha256":
                hashlib.sha256(SRC32.read_bytes()).hexdigest(),
        },
        "method": {
            "seed_order": SEED_ORDER,
            "E_seed_inflation": E_SEED_INFLATION,
            "grid_inflation": GRID_INFLATION,
            "grid": DXI_PRIMARY,
            "error_classes": ["R_sigma (mp35 exact deltas)",
                              "R_cos (1e-12 * weight-sum * trapz|f|)",
                              "R_trap (16U * trapz|g|)",
                              "R_float (1e-11 * trapz scale)",
                              "E_seed (named premise, 10x 600v1200)",
                              "M_grid (named premise, 10x 0.02v0.01 "
                              "channel movement)"],
        },
        "anchors": {
            "a3_seed0_bitwise": True,
            "a4_seed0_exact_gap": a4,
            "a1_bitwise_rows": {
                "%g_%d" % (r["gamma"], r["N"]):
                    r["anchor_bitwise_mismatches"] for r in results},
        },
        "rows": results,
        "producer_go": False, "family_reopened": False, "rh_claim": False,
    }
    (ROOT / "results/2718_gate_sign_rig.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8")
    log("wrote results/2718_gate_sign_rig.json")

    summary = []
    for r in results:
        summary.append({
            "gamma": r["gamma"], "N": r["N"],
            "anchor_mismatches": r.get("anchor_bitwise_mismatches"),
            "branch": r.get("branch_center"),
            "branch_robust": r.get("branch_robust"),
            "claims": [{k: c[k] for k in ("claim", "GREEN_at_premise",
                                          "total_allowance_at_premise",
                                          "E_L_critical",
                                          "ratio_Ecrit_over_Eobs")}
                       for c in r.get("claims", [])],
        })
    print(json.dumps(summary, indent=2))
    ok = (all(r.get("anchor_bitwise_mismatches") == 0 for r in results)
          and all(c["GREEN_at_premise"]
                  and (c["ratio_Ecrit_over_Eobs"] or 0) > 100
                  for r in results for c in r.get("claims", [])))
    print("RESULT 2718 %s" % ("GREEN: all sign claims certified at the "
          "named seed premise with E_crit/E_obs > 100"
          if ok else "NOT GREEN: inspect claims/anchors"))


if __name__ == "__main__":
    main()
