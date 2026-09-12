"""1348 A1b - deep-ladder probe settling the criticality of alpha at the
gate observable (preregistration docs/proofs/1348_a1b_deep_ladder_prg.md,
committed BEFORE any digit, law 42; owner ruling "打吧" 2026-09-12).

Reuse architecture: imports the 1344-A1 module (which imports the 1342
module verbatim) - zero copied arithmetic; the fast sparse prime path is
the G9 bit-identity-certified one. New rung ladder m in {192, 384} with
the NQ rule recomputed (2^18 / 2^19). G10 cross-run reproduction anchors
the ladder on the committed A1 m=96 digit (parsed at runtime from
1344_a1_results.json - constants are DATA). Branch bands (< 0.99 / [0.99,
1.00) / >= 1.00 on the DEEPEST consecutive slope) and the wall-time-only
384-kill are locked in the prereg; no digit may move them.

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
BUDGET_KILL_S = 2.5 * 3600.0      # prereg s4: clock-only, checked at the
HARD_STOP_S = 8.0 * 3600.0        # 192->384 boundary; never reads a digit


def elapsed():
    return time.time() - T0_WALL


def g9_quick(Ps, tag, out):
    """3 random span vectors, verbatim vs G9-certified fast path."""
    rng = np.random.default_rng(1348001)
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
    print(f"== 1348 A1b deep ladder ({mode}) new rungs={list(rungs)} "
          f"QL={QL} R={R_WINDOW!r} numpy={np.__version__} "
          f"mpmath={mpmath.__version__} ==")
    out: dict = dict(record="1348-A1B", mode=mode, model=True,
                     numpy=np.__version__, mpmath=mpmath.__version__,
                     new_rungs=list(rungs))

    # ---------------- anchor block (carried from A1; aborting) ---------- #
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
    gate_g1b = True     # A1 ran the independent-path check; carried as
                        # provenance here (same control, same grid) with a
                        # single re-measure:
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
               G1a=bool(gate_g1a), G1b_carried_from_1344=bool(gate_g1b))
    aborted = None
    if not (gate_g1a and g8c_ok):
        aborted = f"anchor block failure (G1a={gate_g1a}, G8c={g8c_ok})"

    # ---------------- committed A1 ladder digits (constants = DATA) ----- #
    a1 = json.load(open(os.path.join(HERE, "1344_a1_results.json")))
    assert a1["status"].startswith("COMPLETE"), "A1 not COMPLETE in JSON"
    lam_a1 = {int(k): float(v["lambda_min"])
              for k, v in a1["results"].items()}
    out["a1_anchor_digits"] = lam_a1

    results: dict = {}
    lam_192 = None
    killed_384 = False

    # ---------------- G10: cross-run ladder reproduction at m=96 -------- #
    if aborted is None and not SMOKE:
        nq96 = 1 << 17
        p1342._set_grid(nq96)
        Ps96, _ = p1342.build_basis(96)
        if not g9_quick(Ps96, "G9q_2^17", out):
            aborted = "G9-quick failed at 2^17"
        else:
            r96 = p1344.gram_and_min_path(Ps96, {}, p1344.qw_terms_fast)
            lam96 = float(r96["ev"][0])
            rel10 = abs(lam96 / lam_a1[96] - 1.0)
            ok10 = rel10 < 5e-13
            print(f"G10 CROSS-RUN m=96: {lam96:+.9e} vs committed A1 "
                  f"{lam_a1[96]!r}  rel {rel10:.2e}  "
                  f"[{'PASS' if ok10 else 'FAIL'}]")
            out["G10"] = dict(lambda_rerun=lam96, committed=lam_a1[96],
                              rel=rel10, gate=bool(ok10))
            if not ok10:
                aborted = "G10 cross-run reproduction failed - no 192/384 " \
                          "digit trusted (prereg s2)"
    elif SMOKE:
        print("G10 skipped-by-design in SMOKE (no committed smoke digit)")

    # ---------------- new rungs ----------------------------------------- #
    for m in rungs:
        if aborted is not None:
            break
        if m == 384:
            if killed_384:
                break
            if elapsed() > HARD_STOP_S:
                aborted = "hard stop 8h before 384 rung (clock-only)"
                break
            if elapsed() > BUDGET_KILL_S:
                killed_384 = True
                print(f"BUDGET KILL (clock-only, prereg s4): elapsed "
                      f"{elapsed()/3600:.2f} h > 2.5 h -> 384 SKIPPED, "
                      "INCOMPLETE-DEPTH disclosure")
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
        lam = float(r["ev"][0])
        lam2 = float(r["ev"][1]) if len(r["ev"]) > 1 else float("nan")
        g5, pmax = p1344.g5_g7_seeds(Ps, r["B"], p1344.qw_terms_fast)
        gate_g3a = (gl["G3a_rank"] == 3 and gl["G3a_sv_ratio"] < 1e-10
                    and gl["G3a_cond"] > 1e-12)
        gate_g3b = gl["G3b_max_res"] < 1e-9
        gate_g5 = g5 < 1e-9
        gate_g7 = p1344.support_gates(bmeta) and pmax < 1e-9
        escalation = lam <= -1e-8
        gates_m = dict(G3a=bool(gate_g3a), G3b=bool(gate_g3b),
                       G5=bool(gate_g5), G7=bool(gate_g7))
        print(f"   lambda_min = {lam:+.9e}   lambda_2 = {lam2:+.6e}   "
              f"rank {gl['G3a_rank']}/3  null-res {gl['G3b_max_res']:.2e}"
              f"  G5 {g5:.2e}  prime-res {pmax:.2e}  gates "
              + " ".join(f"{k}={'T' if v else 'F'}" for k, v in
                         gates_m.items())
              + ("  ESCALATION-CANDIDATE" if escalation else "")
              + f"  (t={elapsed()/60:.1f} min)")
        results[str(m)] = dict(NQ=nq, wb=wb, lambda_min=lam, lambda2=lam2,
                               eig_low=[float(x) for x in r["ev"][:6]],
                               G3a=gl, G5_max=g5, prime_res_max=pmax,
                               basis=bmeta, gates=gates_m,
                               escalation=bool(escalation))
        if not all(gates_m.values()):
            aborted = f"gate failure at m={m}: {gates_m}"
        if m == 192:
            lam_192 = lam

    # ---------------- slopes + prereg s3 branch -------------------------- #
    lams = dict(lam_a1)
    for k, v in results.items():
        lams[int(k)] = v["lambda_min"]
    ks = sorted(lams)
    pair = {}
    for a, b in zip(ks, ks[1:]):
        if lams[a] > 0 and lams[b] > 0:
            pair[f"{a}->{b}"] = float(-(math.log(lams[b]) - math.log(lams[a]))
                                      / (math.log(b) - math.log(a)))
    sign_stable = all(lams[k] > 0 for k in ks)
    any_esc = (any(v["escalation"] for v in results.values())
               or (lam_192 is not None and lam_192 <= -1e-8))
    fit: dict = dict(pairwise_slopes=pair, sign_stable=bool(sign_stable))
    if sign_stable and not any_esc and len(pair) >= 1:
        deepest_key = f"192->{384}" if "192->384" in pair \
            else ("96->192" if "96->192" in pair else None)
        if deepest_key is None:
            fit["branch"] = "SMOKE/INCOMPLETE (no ladder slope computable)"
        else:
            s_star = pair[deepest_key]
            if s_star < 0.99:
                branch = "SUBCRITICAL-CONFIRMED"
            elif s_star < 1.00:
                branch = "CRITICAL-PINNING"
            else:
                branch = "BOUNDARY-CROSSED"
            mm = np.array(ks, dtype=float)
            ll = np.array([math.log(lams[k]) for k in ks])
            slope_ls, inter = np.polyfit(np.log(mm), ll, 1)
            drift = (pair.get("192->384", float("nan"))
                     - pair.get("96->192", float("nan")))
            fit.update(deepest_pair=deepest_key, s_star=s_star,
                       branch=branch, alpha_ls=float(-slope_ls),
                       c_ls=float(math.exp(inter)),
                       drift_last_minus_prev=float(drift),
                       n_points=len(ks))
            print(f"READOUT: s* = {s_star:.5f} ({deepest_key})   "
                  f"pairwise {pair}   drift {drift:+.5f}   "
                  f"{len(ks)}-pt LSQ alpha {fit['alpha_ls']:.5f}   "
                  f"BRANCH (prereg s3): {branch}")
    elif any_esc:
        fit["branch"] = "ESCALATION-NO-BRANCH (prereg s3 sign-stability " \
                        "precondition failed; digits reported only)"
        print("READOUT:", fit["branch"])
    else:
        fit["branch"] = "INCOMPLETE (abort)"
        print("READOUT: no branch -", aborted)
    out["alpha"] = fit
    out["results"] = results
    out["budget_kill_384"] = bool(killed_384)

    # ---------------- status + sentinel ---------------------------------- #
    g_rollup = dict(G1a=bool(gate_g1a), G8c=bool(g8c_ok),
                    G9q={k: v["gate"] for k, v in out.items()
                         if isinstance(k, str) and k.startswith("G9q")},
                    G10=bool(out.get("G10", {}).get("gate", SMOKE)))
    out["gates"] = g_rollup
    branch = fit.get("branch", "?")
    if SMOKE:
        status = "SMOKE-ONLY"
    elif aborted is not None:
        status = f"ABORTED-UNINFORMATIVE ({aborted})"
    elif any_esc:
        status = f"COMPLETE-ESCALATION ({branch})"
    elif branch.startswith("SMOKE"):
        status = "ABORTED-UNINFORMATIVE (no ladder slope)"
    else:
        status = f"COMPLETE ({branch})" + \
                 (" [DEPTH-LIMITED: 384 budget-killed]" if killed_384
                  else "")
    out["status"] = status
    out["secs"] = round(time.time() - t_start, 1)
    print(f"gates {json.dumps(g_rollup)}")
    print(f"STATUS: {status}")
    fname = os.environ.get(
        "P_OUT", "1348_a1b_smoke_results.json" if SMOKE
        else "1348_a1b_results.json")
    with open(os.path.join(HERE, fname), "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"DONE 1348-A1B  ({mode}, {out['secs']}s, MODEL, certifies "
          "nothing, RH NOT claimed)")


if __name__ == "__main__":
    main()
