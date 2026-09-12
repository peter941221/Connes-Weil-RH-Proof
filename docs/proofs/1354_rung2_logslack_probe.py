"""1354 log-slack rung-II - full-dump re-run of the 1348 deep ladder
(m=192/384) with the gamma(m) = ln(mean/lambda_min)/ln m trajectory
against the 1/3 target. Preregistration
docs/proofs/1354_logslack_extension_prg.md committed BEFORE any
digit (law 42; owner ruling 2026-09-12 "开干" = decision-card option
A). The re-run doubles as the R reproduction gate: lambda_min must
match the committed 1348 digits bit-exactly (rel < 5e-13, digits
parsed at runtime from 1348_a1b_results.json - constants are DATA).
Low-tier means come from 1344_a1_results.json eig_spectrum (also
parsed). Bands in the prereg are locked; nothing here may move them.

Certifies nothing; RH NOT claimed.
"""
import importlib.util
import json
import math
import os
import time

import numpy as np
import mpmath

HERE = os.path.dirname(os.path.abspath(__file__))
SMOKE = os.environ.get("P_SMOKE") == "1"

_spec = importlib.util.spec_from_file_location(
    "p1344", os.path.join(HERE, "1344_a1_m_scaling_probe.py"))
assert _spec is not None and _spec.loader is not None
p1344 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p1344)
p1342 = p1344.p1342

R_WINDOW = p1344.R_WINDOW
QL = p1344.QL
T0_WALL = time.time()
HARD_STOP_S = 4.0 * 3600.0            # prereg s4: clock-only, rung entry
REPRO_TOL = 5e-13                     # prereg s2 R gate
GAMMA_LO = 1.0 / 3.0 - 0.02           # prereg s3 bands, LOCKED
GAMMA_HI = 1.0 / 3.0 + 0.02


def elapsed():
    return time.time() - T0_WALL


def g9_quick(Ps, tag, out):
    """3 random span vectors, verbatim vs G9-certified fast path."""
    rng = np.random.default_rng(1354001)
    worst = 0.0
    for _ in range(3):
        gv = rng.standard_normal(len(Ps)) @ Ps
        d_o = p1342.qw_terms(gv)["qw"]
        d_f = p1344.qw_terms_fast(gv)["qw"]
        worst = max(worst, abs(d_o - d_f) / (1.0 + abs(d_o)))
    ok = worst < 1e-12
    print(f"G9-quick {tag}: worst rel {worst:.2e}  [{'PASS' if ok else 'FAIL'}]")
    out[tag] = dict(worst_rel=worst, gate=bool(ok))
    return ok


def main():
    t_start = time.time()
    mode = "SMOKE" if SMOKE else "OFFICIAL"
    rungs = (6, 8) if SMOKE else (192, 384)
    print(f"== 1354 log-slack rung-II ({mode}) rungs={list(rungs)} "
          f"QL={QL} R={R_WINDOW!r} numpy={np.__version__} "
          f"mpmath={mpmath.__version__} ==")
    out: dict = dict(record="1354-RUNG2", mode=mode, model=True,
                     numpy=np.__version__, mpmath=mpmath.__version__,
                     rungs=list(rungs))

    # ---------------- anchor block (carried verbatim from 1348) ---------- #
    committed_ctrl = None
    md = os.path.join(HERE, "1225_b5_target_satisfiability_audit_"
                          "and_positive_control_preregistration.md")
    if os.path.exists(md):
        import re
        txt = open(md, encoding="utf-8").read()
        vals = sorted(set(re.findall(r"control qw = \+([0-9][0-9.eE+-]*)",
                                     txt)))
        if vals:
            committed_ctrl = float(vals[0])
    p1342._set_grid(1 << 15)
    g_ctrl, ctrl_meta = p1342.build_g_control(0.03)
    qw_ctrl = p1342.qw_terms(g_ctrl, fixed=False)["qw"]
    qw_ctrl_fix = p1342.qw_terms(g_ctrl)["qw"]
    rel_anchor = (abs(qw_ctrl / committed_ctrl - 1.0)
                  if committed_ctrl else float("nan"))
    gate_g1a = committed_ctrl is not None and rel_anchor < 1e-6
    print(f"G1a provenance: {qw_ctrl:+.9e} vs committed {committed_ctrl!r} "
          f"rel {rel_anchor:.2e}  [{'PASS' if gate_g1a else 'FAIL'}]")
    g8ladder_saved = None
    if SMOKE:
        g8ladder_saved = getattr(p1342, "G8_T_LADDER")
        setattr(p1342, "G8_T_LADDER", (400.0, 800.0))
    g8c_ok, g8c_info = p1342.g8_gate(g_ctrl, qw_ctrl_fix,
                                     "control(SMOKE-ladder)" if SMOKE
                                     else "control")
    if g8ladder_saved is not None:
        setattr(p1342, "G8_T_LADDER", g8ladder_saved)
    out.update(control_qw_committed=committed_ctrl,
               control_qw_fixed=qw_ctrl_fix, control_rel=rel_anchor,
               ctrl_meta=ctrl_meta, G8_control=g8c_info,
               G8_ladder=list(getattr(p1342, "G8_T_LADDER")),
               G1a=bool(gate_g1a))
    aborted = None
    if not (gate_g1a and g8c_ok):
        aborted = f"anchor block failure (G1a={gate_g1a}, G8c={g8c_ok})"

    # ---------------- committed data (constants are DATA) ---------------- #
    a1 = json.load(open(os.path.join(HERE, "1344_a1_results.json")))
    assert a1["status"].startswith("COMPLETE"), "A1 not COMPLETE in JSON"
    low_tiers = {}
    for k, v in a1["results"].items():
        eig = [float(x) for x in v["eig_spectrum"]]
        d = len(eig)
        tr = float(np.sum(eig))
        hs2 = float(np.sum(np.square(eig)))
        low_tiers[int(k)] = dict(lambda_min=float(v["lambda_min"]),
                                 mean=tr / d, dim=d, hs2=hs2,
                                 participation=d / (tr * tr / hs2),
                                 from_dump=False)
    lam_deep = {}
    if not SMOKE:
        a1b = json.load(open(os.path.join(HERE, "1348_a1b_results.json")))
        assert a1b["status"].startswith("COMPLETE"), "A1b not COMPLETE"
        lam_deep = {int(k): float(v["lambda_min"])
                    for k, v in a1b["results"].items()}
        out["committed_deep_digits"] = lam_deep
    out["low_tier_stats"] = low_tiers

    # ---------------- rungs ---------------------------------------------- #
    results: dict = {}
    for m in rungs:
        if aborted is not None:
            break
        if elapsed() > HARD_STOP_S:
            aborted = "hard stop 4h at rung entry (clock-only, prereg s4)"
            break
        nq = p1344.choose_nq(m)
        p1342._set_grid(nq)
        Ps, bmeta = p1342.build_basis(m)
        wb = p1344.bump_width(m)
        dx = 2.0 * QL / nq
        print(f"-- m={m}: NQ={nq} (rule: 10*DX={10*dx:.3e} <= "
              f"w_b={wb:.3e})  support_r="
              f"{bmeta['realized_bump_support_radius']:.6f} (bound "
              f"{bmeta['R']:.6f})")
        g9tag = f"G9q_2^{int(math.log2(nq))}"
        if g9tag not in out:
            if not g9_quick(Ps, g9tag, out):
                aborted = f"G9-quick failed at {g9tag}"
                break
        gl: dict = {}
        r = p1344.gram_and_min_path(Ps, gl, p1344.qw_terms_fast)
        ev = np.asarray(r["ev"], dtype=float)   # FULL spectrum, ascending
        lam = float(ev[0])
        lam2 = float(ev[1]) if len(ev) > 1 else float("nan")
        d = int(len(ev))
        tr = float(np.sum(ev))
        mean = tr / d
        hs2 = float(np.sum(ev * ev))
        part = d / (tr * tr / hs2)
        gamma_m = math.log(mean / lam) / math.log(m)
        g5, pmax = p1344.g5_g7_seeds(Ps, r["B"], p1344.qw_terms_fast)
        gate_g3a = (gl["G3a_rank"] == 3 and gl["G3a_sv_ratio"] < 1e-10
                    and gl["G3a_cond"] > 1e-12)
        gate_g3b = gl["G3b_max_res"] < 1e-9
        gate_g5 = g5 < 1e-9
        gate_g7 = p1344.support_gates(bmeta) and pmax < 1e-9
        gates_m = dict(G3a=bool(gate_g3a), G3b=bool(gate_g3b),
                       G5=bool(gate_g5), G7=bool(gate_g7))
        # R gate: cross-run reproduction vs the committed 1348 digit
        repro = dict(applied=False)
        if not SMOKE and m in lam_deep:
            relR = abs(lam / lam_deep[m] - 1.0)
            okR = relR < REPRO_TOL
            repro = dict(applied=True, committed=lam_deep[m],
                         rel=relR, gate=bool(okR))
            print(f"   R REPRO m={m}: {lam:+.9e} vs committed 1348 "
                  f"{lam_deep[m]!r}  rel {relR:.2e}  "
                  f"[{'PASS' if okR else 'FAIL'}]")
            if not okR:
                aborted = ("R reproduction failed at m="
                           f"{m} - CROSS-RUN NONDETERMINISM DISCOVERY, "
                           "no gamma digit trusted (prereg s2/s3)")
        escalation = lam <= -1e-8
        print(f"   lambda_min = {lam:+.9e}   lambda_2 = {lam2:+.6e}   "
              f"mean = {mean:+.6e}   gamma({m}) = {gamma_m:.6f}   "
              f"participation = {part:.4f}   dim={d}   rank "
              f"{gl['G3a_rank']}/3  gates "
              + " ".join(f"{k}={'T' if v else 'F'}" for k, v in
                         gates_m.items())
              + ("  ESCALATION-CANDIDATE" if escalation else "")
              + f"  (t={elapsed()/60:.1f} min)")
        results[str(m)] = dict(NQ=nq, wb=wb, lambda_min=lam, lambda2=lam2,
                               dim=d, tr=tr, mean=mean, hs2=hs2,
                               participation=part, gamma_m=gamma_m,
                               eig_full=[float(x) for x in ev],
                               reproduction=repro,
                               G3a=gl, G5_max=g5, prime_res_max=pmax,
                               basis=bmeta, gates=gates_m,
                               escalation=bool(escalation))
        if not all(gates_m.values()):
            aborted = f"gate failure at m={m}: {gates_m}"
        if repro.get("applied") and not repro.get("gate"):
            break   # never proceed past a reproduction break

    # ---------------- gamma trajectory + prereg s3 band ------------------ #
    any_esc = any(v["escalation"] for v in results.values())
    tiers = dict(low_tiers)
    for k, v in results.items():
        tiers[int(k)] = dict(lambda_min=v["lambda_min"], mean=v["mean"],
                             dim=v["dim"], from_dump=True)
    gamma: dict = dict(per_tier={})
    ks = sorted(tiers)
    ok_tiers = [k for k in ks if tiers[k]["lambda_min"] > 0
                and tiers[k]["mean"] > 0]
    for k in ok_tiers:
        g = math.log(tiers[k]["mean"] / tiers[k]["lambda_min"]) / math.log(k)
        gamma["per_tier"][str(k)] = g
    gamma_5pt = float("nan")
    band = None
    if len(ok_tiers) >= 5 and not any_esc and aborted is None:
        mm = np.array(ok_tiers, dtype=float)
        yy = np.array([math.log(tiers[k]["mean"] / tiers[k]["lambda_min"])
                       for k in ok_tiers])
        slope, inter = np.polyfit(np.log(mm), yy, 1)
        gamma_5pt = float(slope)
        if gamma_5pt < GAMMA_LO:
            band = "TARGET-SURVIVES"
        elif gamma_5pt <= GAMMA_HI:
            band = "ON-TARGET-KNIFE"
        else:
            band = "TARGET-FALSE"
        gamma.update(gamma_5pt=gamma_5pt, band=band, intercept=inter,
                     n_tiers=len(ok_tiers),
                     band_edges=[GAMMA_LO, GAMMA_HI])
        print(f"READOUT: gamma_5pt = {gamma_5pt:.6f} over {len(ok_tiers)} "
              f"tiers   band edges [{GAMMA_LO:.6f},{GAMMA_HI:.6f}]   "
              f"BAND (prereg s3): {band}")
    else:
        gamma["note"] = ("band NOT issued (prereg s3/s4: needs 5 landed "
                         "tiers, R gates passed, no escalation)")
        print("READOUT: no band -", aborted or "insufficient tiers")
    # participation on ALL tiers: low ones re-derived from the committed
    # 1344 full spectra (constants are DATA), deep ones from this dump.
    gamma["participation_by_tier"] = {
        str(k): (results[str(k)]["participation"] if str(k) in results
                 else low_tiers[k]["participation"])
        for k in ks if k in low_tiers or str(k) in results}
    out["gamma"] = gamma
    out["results"] = results
    out["hard_stop_triggered"] = bool(aborted is not None
                                      and "hard stop" in (aborted or ""))

    # ---------------- status + sentinel ---------------------------------- #
    g_rollup = dict(G1a=bool(gate_g1a), G8c=bool(g8c_ok),
                    G9q={k: v["gate"] for k, v in out.items()
                         if isinstance(k, str) and k.startswith("G9q")},
                    R={k: v["reproduction"] for k, v in results.items()
                       if v["reproduction"]["applied"]})
    out["gates"] = g_rollup
    if SMOKE:
        status = "SMOKE-ONLY"
    elif aborted is not None:
        status = f"ABORTED-UNINFORMATIVE ({aborted})"
    elif any_esc:
        status = "COMPLETE-ESCALATION (band not issued)"
    elif band is None:
        status = ("ABORTED-UNINFORMATIVE (no band issuable)"
                  if not out["hard_stop_triggered"]
                  else "DEPTH-LIMITED (band not issued, prereg s4)")
    else:
        status = f"COMPLETE ({band})"
    out["status"] = status
    out["secs"] = round(time.time() - t_start, 1)
    print(f"gates {json.dumps({k: (v if not isinstance(v, dict) else 'see-json') for k, v in g_rollup.items()})}")
    print(f"STATUS: {status}")
    fname = os.environ.get(
        "P_OUT", "1354_rung2_smoke_results.json" if SMOKE
        else "1354_rung2_results.json")
    with open(os.path.join(HERE, fname), "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"DONE 1354-RUNG2  ({mode}, {out['secs']}s, MODEL, certifies "
          "nothing, RH NOT claimed)")


if __name__ == "__main__":
    main()
