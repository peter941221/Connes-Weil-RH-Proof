"""1344 A1 - capacity-scaling probe of the 1342 Gram minimum
lambda_min(m), m in {24, 48, 96} (ESTIMATION class; preregistration =
docs/proofs/1344_b0d_full_charter_attack_the_gate.md section 3 +
implementation amendment section 3a, both committed BEFORE launch, law 42).

Fidelity architecture (amendment 3a):
  * m=24 (reproduce gate) and the resolution-doubling check run the
    1342 code path VERBATIM - this script imports the spent-probe module
    (importlib; module name starts with a digit) and calls its
    gram_and_min / qw_terms directly, zero copied arithmetic.
  * m in {48, 96} run an ALGEBRAICALLY IDENTICAL refactor of the prime
    term only: psum = c . F.real with c the per-grid sparse accumulation
    of the interpolation stencils (same qmax = e^{2*A_DET}, same
    coefficients log(q)/sqrt(q) for primes and log(p)/sqrt(p^k) for prime
    powers k>=2, same linear-interpolation weights on the same QS grid).
    Values equal the verbatim path up to FP sum order (~1e-16 relative).
  * Gate G9 pins the equivalence: at m=24 the FULL Gram is built by both
    paths; max|dB|/(1+|B|) < 1e-12 and |dlambda|/(1+|lambda|) < 1e-12 are
    required before any fast-path digit is admissible.

Reproduce gate: the committed lambda_min is parsed at runtime from
1342_falsifier_results.json (constants are DATA, never hand-typed);
PASS = relative difference < 5e-13, i.e. the committed display digits
+3.083243887e-03 are retained.  FAIL => ABORTED-UNINFORMATIVE and no
new-m digit is trusted (prereg section 3).

Reporting rule (prereg section 3, branches declared pre-digit):
  alpha > 1 with stable sign => CAPACITY-DEAD-MAP registered (model
  level, mirror of 1339); alpha <= 1 => NET-PROGRAM-ALIVE.  No
  FIRE/NO-FIRE bands (estimation probe); lambda_min <= -1e-8 anywhere
  triggers the amendment-3a escalation clause (verbatim-path recheck,
  ESCALATION-CANDIDATE flag, rig-artifact hypothesis first).

Certifies nothing; RH NOT claimed.
"""
import importlib.util
import json
import math
import os
import time

import numpy as np
import mpmath
from scipy.integrate import simpson as _sp_simpson

HERE = os.path.dirname(os.path.abspath(__file__))
SMOKE = os.environ.get("P_SMOKE") == "1"

# ---- import the 1342 module verbatim (name starts with a digit) ---- #
_spec = importlib.util.spec_from_file_location(
    "p1342", os.path.join(HERE, "1342_prime_free_falsifier_probe.py"))
assert _spec is not None and _spec.loader is not None
p1342 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p1342)

R_ROOT = p1342.R_ROOT            # log(2)/2
DELTA = p1342.DELTA              # 0.01
QL = p1342.QL                    # 28.0
R_WINDOW = R_ROOT - DELTA        # committed bump-window radius R

_SPARSE_CACHE: dict[int, np.ndarray] = {}


def bump_width(m: int) -> float:
    """w_b(m) = 0.8 * spacing = 1.6 * R / (m + 1.6), from the committed
    build_basis formulas (Rp = R/(1+1.6/m), s = 2Rp/m, wb = 0.8 s)."""
    return 1.6 * R_WINDOW / (m + 1.6)


def choose_nq(m: int) -> int:
    """Prereg rule: smallest power of two >= floor (2^17 official, 2^15
    smoke) with w_b >= 10 * DX, DX = 2*QL/NQ.  Computed, not assumed."""
    floor = 1 << (15 if SMOKE else 17)
    nq = floor
    wb = bump_width(m)
    while 10.0 * (2.0 * QL / nq) > wb:
        nq *= 2
    return nq


def prime_sparse(nq: int) -> np.ndarray:
    """Sparse coefficient vector c with c . F.real == the verbatim prime
    sum of qw_terms (same terms, same linear-interpolation stencils; only
    the FP summation order differs).  Built once per grid."""
    if nq in _SPARSE_CACHE:
        return _SPARSE_CACHE[nq]
    qs = p1342.QS
    qmax = int(math.exp(2.0 * p1342.A_DET))
    primes = p1342._primes_upto(qmax)
    pf = primes.astype(float)
    lq = np.log(pf)
    # QS is the uniform grid (arange - NQ/2)*DQ, so np.interp's local
    # spacing is exactly DQ at every node: inv = 1/DQ.  (A first draft
    # here had a wrong qs[k]-qs[j0-1] stencil; caught by re-derivation
    # against the verbatim source before launch, F5.)
    inv = np.full(nq, 1.0 / p1342.DQ)
    c = np.zeros(nq)

    def _scatter(x, coeff):
        # replicate np.interp: value = y[i-1]*(1-t) + y[i]*t with
        # i = searchsorted(xp, x, 'right') clamped to [1, n-1]
        i = np.searchsorted(qs, x, side="right")
        np.clip(i, 1, nq - 1, out=i)
        t = (x - qs[i - 1]) * inv[i - 1]
        np.add.at(c, i - 1, coeff * (1.0 - t))
        np.add.at(c, i, coeff * t)

    coeff1 = lq / np.sqrt(pf)
    _scatter(lq, coeff1)
    _scatter(-lq, coeff1)
    # prime powers p^k <= qmax, k >= 2, coefficient log(p)/sqrt(p^k)
    xs, cs = [], []
    for pr in primes:
        pr = int(pr)
        if pr * pr > qmax:
            break
        lp = math.log(pr)
        pk = pr * pr
        while pk <= qmax:
            xs.append(math.log(pk))
            cs.append(lp / math.sqrt(pk))
            pk *= pr
    if xs:
        xa = np.asarray(xs)
        ca = np.asarray(cs)
        _scatter(xa, ca)
        _scatter(-xa, ca)
    _SPARSE_CACHE[nq] = c
    return c


def qw_terms_fast(g):
    """qw_terms with the prime term replaced by the sparse dot product;
    every other line replicates the verbatim 1342 arithmetic (f0, arch via
    simpson_fixed, pole via the two trapezoids)."""
    nq, dq, qs = p1342.NQ, p1342.DQ, p1342.QS
    cvec = np.conj(g[(-np.arange(nq)) % nq])
    F = p1342.circular_conv_centered(g, cvec)
    f0 = float((np.abs(g) ** 2).sum() * dq)
    pos0 = nq // 2
    yp = qs[pos0:]
    Fp = F[pos0:]
    Fm = F[(nq - np.arange(pos0, nq)) % nq]
    num = np.exp(yp / 2) * (Fp + Fm) - 2 * f0
    integ = np.empty_like(num)
    integ[1:] = num[1:] / (2 * np.sinh(yp[1:]))
    integ[0] = f0 / 2.0
    tail = f0 * math.log(math.tanh(yp[-1] / 2))
    arch = p1342.LOG4PI_GAMMA * f0 + p1342.simpson_fixed(integ.real, dq) + tail
    psum = float(prime_sparse(nq) @ F.real)
    pole = float(np.real(np.trapezoid(np.exp(qs / 2) * F, dx=dq)
                         + np.trapezoid(np.exp(-qs / 2) * F, dx=dq)))
    return dict(f0=f0, arch=arch, prime=psum, pole=pole,
                qw=pole - arch - psum)


def gram_and_min_path(Ps, gate_logs, qwfunc):
    """Replica of p1342.gram_and_min with an injectable qw function
    (G9 cross-checks this body against the verbatim module function at
    m=24, so replication drift is gate-caught)."""
    m = len(Ps)
    B = np.zeros((m, m))
    for i in range(m):
        B[i, i] = qwfunc(Ps[i])["qw"]
        for j in range(i):
            b = (qwfunc(Ps[i] + Ps[j])["qw"]
                 - qwfunc(Ps[i] - Ps[j])["qw"]) / 4.0
            B[i, j] = B[j, i] = b
    C, sg = p1342.vanishing_matrix(Ps)
    Z, sv, rk = p1342.nullspace(C)
    gate_logs["G3a_sv_ratio"] = float(sv[rk] / sv[0]) if rk < len(sv) else 0.0
    gate_logs["G3a_cond"] = float(sv[2] / sv[0])
    gate_logs["G3a_rank"] = rk
    res = []
    dq, qs = p1342.DQ, p1342.QS
    for k in range(Z.shape[1]):
        gk = Z[:, k] @ Ps
        E = np.exp(np.outer(sg, qs))
        res.extend(np.abs(dq * (E @ gk)) / max(np.abs(gk).max(), 1e-300))
    gate_logs["G3b_max_res"] = float(max(res))
    Gm = Z.T @ B @ Z
    Gm = (Gm + Gm.T) / 2
    ev, W = np.linalg.eigh(Gm)
    return dict(B=B, C=C, Z=Z, Gm=Gm, ev=ev, W=W, sv=sv, rk=rk)


def g5_g7_seeds(Ps, B, qwfunc):
    """G5 gram-vs-operator identity on the three committed seeds over the
    full span; G7's prime-residue leg rides on the same evaluations."""
    g5 = 0.0
    pmax = 0.0
    for seed in (1342001, 1342002, 1342003):
        rng = np.random.default_rng(seed)
        qq = rng.standard_normal(len(Ps))
        gq = qq @ Ps
        d = qwfunc(gq)
        g5 = max(g5, abs(qq @ B @ qq - d["qw"]) / (1.0 + abs(d["qw"])))
        pmax = max(pmax, abs(d["prime"]))
    return g5, pmax


def support_gates(bmeta):
    """G7 support leg (G2 of 1342, basis-level): realized bump support
    inside the committed window and square-radius proxy strictly below
    the first prime log 2 (prime-free lemma C1SameOwnerWeil.lean:167-189)."""
    ok_r = bmeta["realized_bump_support_radius"] <= bmeta["R"] + 1e-12
    ok_p = bmeta["square_radius_proxy"] <= math.log(2.0) - 1e-12
    return bool(ok_r and ok_p)


def main():
    t0 = time.time()
    mode = "SMOKE" if SMOKE else "OFFICIAL"
    ms = (4, 6) if SMOKE else (24, 48, 96)
    print(f"== 1344 A1 m-scaling probe ({mode}) m={list(ms)} QL={QL} "
          f"R={R_WINDOW!r} numpy={np.__version__} mpmath={mpmath.__version__} ==")
    out: dict = dict(record="1344-A1", mode=mode, model=True,
                     numpy=np.__version__, mpmath=mpmath.__version__,
                     QL=QL, R_window=R_WINDOW, m_list=list(ms))

    # ---------- anchor block: G1a/G1b provenance + G8c (once; the
    # control is m-independent, amendment 3a) ---------- #
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
    p1342._set_grid(1 << 15)                     # anchor grid (inv11b)
    g_ctrl, ctrl_meta = p1342.build_g_control(0.03)
    qw_ctrl = p1342.qw_terms(g_ctrl, fixed=False)["qw"]   # G1a broken path
    qw_ctrl_fix = p1342.qw_terms(g_ctrl)["qw"]            # corrected kernel
    rel_anchor = (abs(qw_ctrl / committed_ctrl - 1.0)
                  if committed_ctrl else float("nan"))
    gate_g1a = committed_ctrl is not None and rel_anchor < 1e-6
    pos0 = p1342.NQ // 2
    yp = p1342.QS[pos0:]
    cvec = np.conj(g_ctrl[(-np.arange(p1342.NQ)) % p1342.NQ])
    Fc = p1342.circular_conv_centered(g_ctrl, cvec)
    f0c = float((np.abs(g_ctrl) ** 2).sum() * p1342.DQ)
    numc = np.exp(yp / 2) * (Fc[pos0:]
                             + Fc[(p1342.NQ - np.arange(pos0, p1342.NQ))
                                  % p1342.NQ]) - 2 * f0c
    integc = np.empty_like(numc)
    integc[1:] = numc[1:] / (2 * np.sinh(yp[1:]))
    integc[0] = f0c / 2.0
    tailc = f0c * math.log(math.tanh(yp[-1] / 2))
    arch_sp = p1342.LOG4PI_GAMMA * f0c + float(_sp_simpson(
        integc.real[:-1], dx=p1342.DQ)) \
        + 0.5 * p1342.DQ * (integc.real[-1] + integc.real[-2]) + tailc
    arch_fx = (p1342.LOG4PI_GAMMA * f0c
               + p1342.simpson_fixed(integc.real, p1342.DQ) + tailc)
    g1b_dev = abs(arch_sp - arch_fx) / max(abs(arch_fx), 1e-300)
    gate_g1b = g1b_dev < 1e-9
    print(f"G1a provenance (broken rule): recomputed {qw_ctrl:+.9e} vs "
          f"committed {committed_ctrl!r}  rel {rel_anchor:.2e}  "
          f"[{'PASS' if gate_g1a else 'FAIL'}]")
    print(f"G1b corrected control qw = {qw_ctrl_fix:+.9e}  "
          f"(independent-path arch dev {g1b_dev:.2e})  "
          f"[{'PASS' if gate_g1b else 'FAIL'}]")
    if SMOKE:
        # SMOKE-ONLY reduced ladder: exercises the zeros/psi machinery
        # without the official truncation budget (never used for digits)
        saved = getattr(p1342, "G8_T_LADDER")
        setattr(p1342, "G8_T_LADDER", (400.0, 800.0))
        g8c_ok, g8c_info = p1342.g8_gate(g_ctrl, qw_ctrl_fix,
                                         "control(SMOKE-ladder)")
        setattr(p1342, "G8_T_LADDER", saved)
    else:
        g8c_ok, g8c_info = p1342.g8_gate(g_ctrl, qw_ctrl_fix, "control")
    out.update(control_qw_committed=committed_ctrl,
               control_qw_fixed=qw_ctrl_fix,
               control_qw_broken_recomputed=qw_ctrl, control_rel=rel_anchor,
               G1b_arch_dev=g1b_dev, ctrl_meta=ctrl_meta,
               G8_control=g8c_info, G8_ladder=list(p1342.G8_T_LADDER))

    # ---------- committed lambda_min for the reproduce gate ---------- #
    lam_committed = None
    j1342 = os.path.join(HERE, "1342_falsifier_results.json")
    if os.path.exists(j1342):
        lam_committed = json.load(open(j1342))["lambda_min"]
    out["lambda_min_committed_1342"] = lam_committed

    results: dict = {}
    aborted = None
    lam24_orig = None
    nq24 = None

    for m in ms:
        nq = choose_nq(m)
        p1342._set_grid(nq)
        Ps, bmeta = p1342.build_basis(m)
        wb = bump_width(m)
        dx = 2.0 * QL / nq
        print(f"-- m={m}: NQ={nq} (rule: 10*DX={10*dx:.3e} <= "
              f"w_b={wb:.3e})  support_r="
              f"{bmeta['realized_bump_support_radius']:.6f} (bound "
              f"{bmeta['R']:.6f})")
        gl: dict = {}
        use_fast = SMOKE or m != 24
        if not use_fast:
            r = p1342.gram_and_min(Ps, gl)         # VERBATIM 1342 path
        else:
            r = gram_and_min_path(Ps, gl, qw_terms_fast)
        lam = float(r["ev"][0])
        lam2 = float(r["ev"][1]) if len(r["ev"]) > 1 else float("nan")
        qwf = qw_terms_fast if use_fast else p1342.qw_terms
        g5, pmax = g5_g7_seeds(Ps, r["B"], qwf)
        gate_g3a = (gl["G3a_rank"] == 3 and gl["G3a_sv_ratio"] < 1e-10
                    and gl["G3a_cond"] > 1e-12)
        gate_g3b = gl["G3b_max_res"] < 1e-9
        gate_g5 = g5 < 1e-9
        gate_g7 = support_gates(bmeta) and pmax < 1e-9
        escalation = lam <= -1e-8
        esc_orig = None
        if escalation and use_fast and not SMOKE:
            # amendment 3a: verbatim-path recheck before any trust
            print(f"   !! lambda_min <= -1e-8: ESCALATION recheck on the "
                  f"verbatim path (may exceed budget, authorized 3a)")
            r_o = p1342.gram_and_min(Ps, {})
            esc_orig = float(r_o["ev"][0])
        gates_m = dict(G3a=bool(gate_g3a), G3b=bool(gate_g3b),
                       G5=bool(gate_g5), G7=bool(gate_g7))
        print(f"   lambda_min = {lam:+.9e}   lambda_2 = {lam2:+.6e}   "
              f"rank {gl['G3a_rank']}/3  sv-ratio {gl['G3a_sv_ratio']:.2e}"
              f"  null-res {gl['G3b_max_res']:.2e}  G5 {g5:.2e}  "
              f"prime-res {pmax:.2e}  gates "
              + " ".join(f"{k}={'T' if v else 'F'}"
                         for k, v in gates_m.items())
              + ("  ESCALATION-CANDIDATE" if escalation else ""))
        results[str(m)] = dict(NQ=nq, wb=wb, DX=dx, lambda_min=lam,
                               lambda2=lam2, fast_path=bool(use_fast),
                               eig_spectrum=[float(x) for x in r["ev"]],
                               G3a=gl, G3b_max_res=gl["G3b_max_res"],
                               G5_max=g5, prime_res_max=pmax,
                               basis=bmeta, gates=gates_m,
                               escalation=bool(escalation),
                               escalation_verbatim_lambda=esc_orig)
        if not all(gates_m.values()) or (escalation and esc_orig is not None
                                         and esc_orig <= -1e-8):
            if not all(gates_m.values()):
                aborted = f"gate failure at m={m}: {gates_m}"
            else:
                # confirmed negative on BOTH paths = escalation candidate
                # (digits reported; adjudication belongs to a NEW prereg)
                aborted = None
                print("   escalation confirmed on verbatim path - digits "
                      "reported, no A1 verdict band applies (3a)")
            break
        if m == 24 and not SMOKE:
            lam24_orig = lam
            nq24 = nq
            # ----- reproduce gate (prereg section 3) ----- #
            rel = (abs(lam / lam_committed - 1.0)
                   if lam_committed else float("nan"))
            ok = lam_committed is not None and rel < 5e-13
            print(f"REPRODUCE m=24: {lam:+.9e} vs committed "
                  f"{lam_committed!r}  rel {rel:.2e}  "
                  f"[{'PASS' if ok else 'FAIL'}]")
            out["reproduce"] = dict(lambda_min=lam,
                                    committed=lam_committed, rel=rel,
                                    gate=bool(ok))
            if not ok:
                aborted = "REPRODUCE gate failed - no new-m digit trusted"
                break
            # ----- G9: fast-path equivalence on the FULL m=24 Gram ----- #
            r_fast = gram_and_min_path(Ps, {}, qw_terms_fast)
            dB = float(np.max(np.abs(r_fast["B"] - r["B"])
                              / (1.0 + np.abs(r["B"]))))
            dl = abs(float(r_fast["ev"][0]) - lam) / (1.0 + abs(lam))
            g9 = dB < 1e-12 and dl < 1e-12
            print(f"G9 path-equivalence: max|dB|/(1+|B|) {dB:.2e}  "
                  f"|dlam|/(1+|lam|) {dl:.2e}  "
                  f"[{'PASS' if g9 else 'FAIL'}]")
            out["G9"] = dict(dB=dB, dlambda=dl, gate=bool(g9),
                             lambda_fast=float(r_fast["ev"][0]))
            if not g9:
                aborted = ("G9 failed - fast-path digits inadmissible, "
                           "m=48/96 not run")
                break

    # ---------- SMOKE-only quick two-path cross-check (machinery gate;
    # the official equivalence gate is G9 on the full m=24 Gram) ---------- #
    if SMOKE:
        p1342._set_grid(1 << 15)
        Psq, _ = p1342.build_basis(4)
        rng = np.random.default_rng(1344001)
        worst = 0.0
        for _ in range(3):
            gv = rng.standard_normal(len(Psq)) @ Psq
            d_orig = p1342.qw_terms(gv)["qw"]
            d_fast = qw_terms_fast(gv)["qw"]
            worst = max(worst, abs(d_orig - d_fast) / (1.0 + abs(d_orig)))
        g9s = worst < 1e-12
        print(f"G9-smoke two-path qw cross-check: worst rel {worst:.2e}  "
              f"[{'PASS' if g9s else 'FAIL'}]")
        out["G9"] = dict(smoke_worst_rel=worst, gate=bool(g9s))

    # ---------- doubling check at m=24 (verbatim path, G4-style) ---------- #
    if (not SMOKE and aborted is None and lam24_orig is not None
            and nq24 is not None):
        p1342._set_grid(2 * nq24)
        Ps2, _ = p1342.build_basis(24)
        r2 = p1342.gram_and_min(Ps2, {})
        lam_d = float(r2["ev"][0])
        p1342._set_grid(nq24)
        d_lam = abs(lam_d - lam24_orig)
        g4 = d_lam < 1e-8
        print(f"DOUBLING m=24 (NQ {nq24}->{2*nq24}, verbatim path): "
              f"lambda_min {lam24_orig:+.9e} -> {lam_d:+.9e}  delta "
              f"{d_lam:.2e}  [{'PASS' if g4 else 'FAIL'}]")
        out["doubling"] = dict(lambda_min_doubled=lam_d, delta=d_lam,
                               gate=bool(g4))
        if not g4:
            aborted = "doubling stability gate failed"

    # ---------- alpha fit + preregistered branches ---------- #
    fit: dict = {}
    lams = {int(k): v["lambda_min"] for k, v in results.items()}
    sign_stable = all(x > 0 for x in lams.values())
    if sign_stable and len(lams) == len(ms) and aborted is None:
        mm = np.array(sorted(lams), dtype=float)
        ll = np.log(np.array([lams[int(k)] for k in sorted(lams)]))
        slope, intercept = np.polyfit(np.log(mm), ll, 1)[0], \
            np.polyfit(np.log(mm), ll, 1)[1]
        alpha3 = float(-slope)
        ks = sorted(lams)
        pair = {}
        for a, b in zip(ks, ks[1:]):
            pair[f"{a}->{b}"] = float(-(math.log(lams[b]) - math.log(lams[a]))
                                      / (math.log(b) - math.log(a)))
        branch = ("CAPACITY-DEAD-MAP" if alpha3 > 1.0
                  else "NET-PROGRAM-ALIVE")
        fit = dict(alpha_3pt=alpha3, c=float(math.exp(intercept)),
                   alpha_pairwise=pair, sign_stable=True, branch=branch)
        print(f"ALPHA fit: lambda_min(m) ~ {math.exp(intercept):.6e} * "
              f"m^(-{alpha3:.4f})   pairwise {pair}   "
              f"BRANCH (prereg s3): {branch}")
    else:
        fit = dict(sign_stable=bool(sign_stable),
                   branch="SIGN-UNSTABLE (escalation clause 3a)"
                   if not sign_stable else "INCOMPLETE (abort)")
        print(f"ALPHA fit not performed: {fit['branch']}")
    out["alpha"] = fit
    out["results"] = results

    per_m_gates = {k: v["gates"] for k, v in results.items()}
    per_m_ok = all(all(g.values()) for g in per_m_gates.values())
    top_ok = all([bool(gate_g1a), bool(gate_g1b), bool(g8c_ok),
                  bool(out.get("G9", {}).get("gate", SMOKE)),
                  bool(out.get("reproduce", {}).get("gate", SMOKE)),
                  bool(out.get("doubling", {}).get("gate", SMOKE))])
    allg = dict(G1a=bool(gate_g1a), G1b=bool(gate_g1b), G8c=bool(g8c_ok),
                G9=bool(out.get("G9", {}).get("gate", SMOKE)),
                reproduce=bool(out.get("reproduce", {}).get("gate", SMOKE)),
                doubling=bool(out.get("doubling", {}).get("gate", SMOKE)),
                per_m=per_m_gates)
    flat_ok = top_ok and per_m_ok
    out["gates"] = allg
    if SMOKE:
        status = "SMOKE-ONLY"
    elif aborted is not None:
        status = f"ABORTED-UNINFORMATIVE ({aborted})"
    elif not flat_ok:
        status = "ABORTED-UNINFORMATIVE (gate roll-up)"
    else:
        status = f"COMPLETE ({fit.get('branch', '?')})"
    out["status"] = status
    out["secs"] = round(time.time() - t0, 1)
    print(f"gates {json.dumps(allg)}")
    print(f"STATUS: {status}")
    fname = os.environ.get(
        "P_OUT", "1344_a1_smoke_results.json" if SMOKE
        else "1344_a1_results.json")
    with open(os.path.join(HERE, fname), "w") as fh:
        json.dump(out, fh, indent=1)
    if SMOKE and flat_ok:
        print("SMOKE-MACHINERY-GREEN")
    print(f"DONE 1344-A1  ({mode}, {out['secs']}s, MODEL, certifies "
          "nothing, RH NOT claimed)")


if __name__ == "__main__":
    main()
