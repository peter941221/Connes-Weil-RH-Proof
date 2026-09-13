#!/usr/bin/env python3
"""1403 — RUNG-3 ROUTE-BETA EXACT-ANCHOR PROBE (prereg
docs/proofs/1403_beta_anchor_exact_probe_prereg.md).

Object: A_beta(rho) = arch h_rho.convolutionSquare on the 7-node
symmetric root-window interpolant (records 1083/1084/1085 final form;
recon 1402).  Instrument: run_1398_rig (the certified v3 chain) is
IMPORTED; everything dimension-free (J_master, S_mp, F_at, compute_A,
gv_scale, band_of_A, laplace_g, _S_np, _panels, all tolerance
constants) is used UNCHANGED.  The two beta-forced changes are exactly
the prereg's: n=7 (gram7/lambda_min7/solve_factor7 transcribed
character-for-character from the 1398 4-node originals) and ONE
factor (SingleOwner supplies .g/.Cg/.Rs/.Rg/.nodes so the imported
float64 evaluator layer sees a compatible owner).

The window is LOCKED at log2/2 (no grid; the support obligation of the
root window), eps locked 0.01 with one informational eps=0.1 variant
at tier-1 (F14-beta re-test; the prereg section-5 audit shows delta
sub-ulp at every cohort point).

Law 42: committed before any anchor digit.  RH not claimed.
"""
import hashlib
import json
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402
import mpmath as mp  # noqa: E402

mp.mp.prec = 200
import run_1398_rig as R  # noqa: E402  (the locked 1398 v3 instrument)

M, MC = mp.mpf, mp.mpc
RSTR = "0.34657359027997264"          # log(2)/2, float64 literal (prereg 1)
RW = M(RSTR)
EPS = M("0.01")                        # locked (prereg section 1)
RRS = (0.55, 0.6, 0.75, 0.9, 0.99)
IMS = (14.134725, 21.022040, 25.010858, 100.0, 1054.0)
TIER1 = (0.99, 14.134725)
BATTERY = {(0.99, 100.0), (0.99, 1054.0)}   # tier-3 cells
TARGETS = [MC(0), MC(0), MC(0), MC(1), MC(-1), MC(0), MC(0)]
GI_MP_TOL = 1e-15                    # 1403 v2 clause (was 1e-30 in v1)
N = 7
T0 = time.time()


def stamp(msg):
    print(f"[{time.time() - T0:7.1f}s] {msg}", flush=True)


def nodes7(rr, im):
    rho = MC(str(rr), str(im))
    return [M(0), -MC("0.5"), MC("0.5"), rho, -rho, M(1), M(-1)]


# ------------------------------------------- n=7 transcriptions of 1398 code
def gram7(s):
    """r13.gram verbatim, dimension 7 (same kernel, same branches)."""
    G = mp.zeros(N, N)
    for i in range(N):
        for j in range(N):
            a = s[i] + mp.conj(s[j])
            G[i, j] = 2 * RW if a == 0 else 2 * mp.sinh(a * RW) / a
    return G


def lambda_min7(G):
    """R.lambda_min_mp verbatim, dimension 7."""
    lo, hi = M(0), M(mp.re(sum(G[i, i] for i in range(N))))

    def ld_pd(mu):
        A = mp.zeros(N, N)
        for i in range(N):
            for j in range(N):
                A[i, j] = G[i, j]
            A[i, i] -= mu
        for c in range(N):
            for r in range(c + 1, N):
                f = A[r, c] / A[c, c]
                for k in range(c, N):
                    A[r, k] -= f * A[c, k]
        return all(mp.re(A[i, i]) > 0 for i in range(N))

    assert ld_pd(lo)
    for _ in range(150):
        mu = (lo + hi) / 2
        if ld_pd(mu):
            lo = mu
        else:
            hi = mu
    return lo


def solve_factor7(nodes, p, eps=EPS, alpha_scale=1):
    """R.solve_factor verbatim: dimension 7, one factor, window RW."""
    G = gram7(nodes)
    alpha = lambda_min7(G) * M(str(alpha_scale))
    TB = sum(mp.exp(mp.fabs(n) * RW) for n in nodes)
    Delta = eps * alpha / (4 * (1 + eps) * TB ** 2)
    delta = min(RW / 2, Delta)
    rIn, rOut = RW - delta, RW - delta / 2
    T = mp.zeros(N, N)
    jc = {}
    betas = []
    for i in range(N):
        for j in range(N):
            A = nodes[i] + mp.conj(nodes[j])
            if A == 0:
                T[i, j] = 2 * rIn + delta / 2
            else:
                b1, b2 = A * delta / 2, -A * delta / 2
                for bb in (b1, b2):
                    if bb not in jc:
                        jc[bb] = R.J_master(bb, 'J')
                    betas.append(bb)
                T[i, j] = (2 * mp.sinh(A * rIn) / A
                           + (delta / 2) * (mp.e ** (A * rIn) * jc[b1]
                                            + mp.e ** (-A * rIn) * jc[b2]))
    # the 1398 inv1 mpmath trap (law F13): nested constructor + assert
    rhs = mp.matrix([[v] for v in p])
    assert all(rhs[i, 0] == p[i] for i in range(N)), "rhs construction lost p"
    coeff = mp.lu_solve(T, rhs)
    resid = max(abs(sum(T[i, j] * coeff[j, 0] for j in range(N)) - p[i])
                for i in range(N))
    return dict(nodes=nodes, G=G, alpha=alpha, TB=TB, Delta=Delta,
                delta=delta, rIn=rIn, rOut=rOut, T=T, coeff=coeff,
                resid=resid, betas=betas,
                c64=np.array([complex(coeff[i, 0]) for i in range(N)]),
                rIn64=float(rIn), rOut64=float(rOut), delta64=float(delta))


class SingleOwner:
    """prereg section 1: h(x) = tau(x) * sum_i c_i e^{conj(s_i) x} on the
    tapered window; exposes exactly the fields the IMPORTED float64 layer
    (F_at / compute_A / laplace_g) consumes: .g, .Cg, .Rs, .Rg, .nodes."""

    def __init__(self, fac):
        self.fac = fac
        self.nodes = fac['nodes']
        self.mode = np.array([np.conj(complex(n)) for n in self.nodes])
        self.c64 = fac['c64']
        self.rIn, self.rOut = fac['rIn64'], fac['rOut64']
        self.d2 = max(fac['delta64'] / 2.0, 1e-300)
        self.Rs = self.rOut
        self.Rg = float(RW)                     # support of F = 2Rg = log2
        self.Cg = np.array([-self.rOut, 0.0, self.rOut])

    def g(self, xs):
        xs = np.asarray(xs, dtype=np.float64)
        tau = R._S_np((self.rOut - np.abs(xs)) / self.d2)
        out = np.zeros(xs.shape, dtype=np.complex128)
        for i in range(N):
            out += self.c64[i] * np.exp(self.mode[i] * xs)
        return tau * out


# ------------------------------------------------------------- cell runner
def gd_errors(own):
    """GD-beta: |lap h(s_j) - target_j| at ALL SEVEN nodes."""
    errs = []
    for j in range(N):
        lv = R.laplace_g(own, complex(own.nodes[j]))
        errs.append(abs(lv - complex(TARGETS[j])))
    return max(errs), errs


def gi_check7(own, fac):
    """GI-beta (amended prereg section 3): reassemble L_j^{mp} from the
    solved coefficients via the conjugated kernel; then tie the float
    evaluator to the mp convention."""
    c, s = fac['coeff'], fac['nodes']
    worst_mp, worst_fl = M(0), 0.0
    for j in range(N):
        Lj = sum(c[i, 0] * R_W(mp.conj(s[i]) + s[j]) for i in range(N))
        worst_mp = max(worst_mp, abs(Lj - TARGETS[j]))
        worst_fl = max(worst_fl, abs(R.laplace_g(own, complex(s[j]))
                                     - complex(Lj)))
    return float(worst_mp), worst_fl


def R_W(a):
    """int_{-R}^{R} e^{a x} dx, same closed form + branch as gram7."""
    return 2 * RW if a == 0 else 2 * mp.sinh(a * RW) / a


def run_cell(rr, im, full=False, eps=None):
    eps = EPS if eps is None else eps
    fac = solve_factor7(nodes7(rr, im), TARGETS, eps=eps)
    own = SingleOwner(fac)
    A, F0, S = R.compute_A(own)
    gdmax, gdall = gd_errors(own)
    out = dict(geo=(rr, im), A=float(A), F0=complex(F0), S=float(S),
               gs_ok=bool(fac['resid'] <= R.GS_TOL),
               resid=float(fac['resid']), alpha=float(fac['alpha']),
               TB=float(fac['TB']), delta=float(fac['delta']),
               Delta=float(fac['Delta']),
               cnorm=max(abs(x) for x in fac['c64']),
               gdmax=float(gdmax), gdall=[float(x) for x in gdall])
    if not full:
        return out
    out['F0_npw24'] = R.F_at(own, 0.0, 24)
    A64, _, _ = R.compute_A(own, 64)
    A96, _, _ = R.compute_A(own, 96)
    out['A64'], out['A96'] = float(A64), float(A96)
    out['A_R'] = 2.0 * float(A64) - float(A)
    # GQ: target x2 -> coefficients double -> F quadruples -> A quadruples
    fac2 = solve_factor7(nodes7(rr, im), [2 * t for t in TARGETS], eps=eps)
    A2, _, _ = R.compute_A(SingleOwner(fac2))
    out['A_quadr'] = float(A2)
    sym, pair, jh = R.gt_tier1(fac, fac)          # dimension-free identities
    out['gt_sym'], out['gt_pair'], out['gt_jh'] = sym, pair, jh
    gi_mp, gi_fl = gi_check7(own, fac)
    out['gi_mp'], out['gi_fl'] = gi_mp, gi_fl
    facH = solve_factor7(nodes7(rr, im), TARGETS, eps=eps, alpha_scale=0.5)
    AH, _, _ = R.compute_A(SingleOwner(facH))
    out['A_alpha2'] = float(AH)
    return out


def gf_ok(r):
    return (r['F0'].real > 0
            and abs(r['F0'].imag) <= R.GF_IM_TOL * abs(r['F0'].real)
            and abs(r['F0_npw24'].real - r['F0'].real)
            <= R.GF_RE_TOL * abs(r['F0'].real))


def main():
    cells = [(rr, im) for im in IMS for rr in RRS]
    assert len(cells) == 25 and TIER1 in cells
    out_cells, gates, t1 = [], {}, None
    validity = ['G0', 'GI', 'GS', 'GT', 'GF', 'GD', 'GR', 'GQ']

    # G0-beta: admissibility (definitional assertion, prereg section 3)
    g0 = all(0.5 < rr <= 0.99 for rr, _ in cells)
    gates['G0'] = 'PASS' if g0 else 'FAIL'
    run_void = not g0

    if not run_void:
        stamp(f"tier-1 {TIER1}")
        t1 = run_cell(*TIER1, full=True)
        # informational F14-beta re-test: eps 0.1 vs 0.01 at tier-1
        e1 = run_cell(*TIER1, eps=M("0.1"))
        t1['A_eps01'] = e1['A']
        gt = (t1['gt_sym'] <= R.GT_SYM_TOL and t1['gt_pair'] <= R.GT_PAIR_TOL
              and t1['gt_jh'] <= R.GT_JH_TOL)
        gd = t1['gdmax'] <= R.GD_TOL
        gr = abs(t1['A64'] - t1['A']) <= R.GR_TOL * abs(t1['A'])
        gq = abs(t1['A_quadr'] - 4 * t1['A']) <= R.GQ_TOL * abs(4 * t1['A'])
        # 1403 v2: clause-1 class 1e-15 (band-term bound delta*||c||*R
        # <= 5.6e-15 from the v1 audit table; convention errors enter at
        # O(1)).  Clause 2 is an O(1) lap difference: the GD class.
        gi = t1['gi_mp'] <= GI_MP_TOL and t1['gi_fl'] <= R.GD_TOL
        for name, ok in (('GI', gi), ('GS', t1['gs_ok']), ('GT', gt),
                         ('GF', gf_ok(t1)), ('GD', gd), ('GR', gr),
                         ('GQ', gq)):
            gates[name] = 'PASS' if ok else 'FAIL'
        run_void = any(gates[k] != 'PASS' for k in validity)
        stamp(f"tier-1 A={t1['A']:.10e} S={t1['S']:.3e} F0={t1['F0']:.6e} "
              f"gdmax={t1['gdmax']:.2e} gi=({t1['gi_mp']:.1e},"
              f"{t1['gi_fl']:.1e}) gates={gates}")
        stamp(f"tier-1 extras: A64={t1['A64']:.6e} A96={t1['A96']:.6e} "
              f"A_R={t1['A_R']:.6e} A2v={t1['A_quadr']:.6e} "
              f"A_eps0.1={t1['A_eps01']:.10e} A_alpha2={t1['A_alpha2']:.6e} "
              f"gt=({t1['gt_sym']:.1e},{t1['gt_pair']:.1e},"
              f"{t1['gt_jh']:.1e}) delta={t1['delta']:.3e}")
        if not run_void:
            out_cells.append(('tier1', t1, R.band_of_A(t1['A'], t1['S'])))
            for (rr, im) in cells:
                if (rr, im) == TIER1:
                    continue
                r = run_cell(rr, im, full=(rr, im) in BATTERY)
                bad = ((not r['gs_ok']) or not (
                    r['F0'].real > 0
                    and abs(r['F0'].imag) <= R.GF_IM_TOL * abs(r['F0'].real)
                ) or r['gdmax'] > R.GD_TOL)
                band = 'BADCELL' if bad else R.band_of_A(r['A'], r['S'])
                out_cells.append((('tier3' if (rr, im) in BATTERY
                                   else 'tier2'), r, band))
                stamp(f"cell ({rr},{im}): A={r['A']:.6e} S={r['S']:.3e} "
                      f"F0={r['F0'].real:.4e} gdmax={r['gdmax']:.2e} "
                      f"band={band}")
            run_void = any(gates[k] != 'PASS' for k in validity)

    npos = sum(1 for _, _, b in out_cells if b == 'POS')
    sneg = sum(1 for _, _, b in out_cells if b == 'NEG')
    ntie = sum(1 for _, _, b in out_cells if b == 'TIE')
    nbad = sum(1 for _, _, b in out_cells if b == 'BADCELL')
    witness = next((r['geo'] for _, r, b in out_cells if b == 'POS'), None)
    if run_void:
        print("VERDICT betaAnchorWitness=NONE cells=VOID", flush=True)
    else:
        w = ("NONE" if witness is None else
             f"rho={witness[0]}+{witness[1]}I")
        print(f"VERDICT betaAnchorWitness={w} cells=POS:{npos},NEG:{sneg},"
              f"TIE:{ntie},BAD:{nbad}", flush=True)
    parts = ",".join(f"{k}:{gates.get(k, 'SKIP')}" for k in validity)
    print(f"DONE gates={parts}", flush=True)

    res = dict(wall_s=time.time() - T0,
               tier1=_ser(t1) if t1 is not None else None,
               cohort=25, tested=len(out_cells),
               census=dict(POS=npos, NEG=sneg, TIE=ntie, BAD=nbad),
               witness=list(witness) if witness else None,
               void=run_void, gates=gates,
               cells=[dict(kind=k, **_ser(r), band=b)
                      for k, r, b in out_cells])
    with open("docs/proofs/1403_rig_results.json", 'w') as fh:
        json.dump(res, fh, indent=1, default=str)
    with open("docs/proofs/1403_rig_cells.tsv", 'w') as fh:
        fh.write("kind\tRERHO\tIMRHO\talpha\tTB\tdelta\tDelta\tcnorm\tresid\t"
                 "ReF0\tImF0\tA\tS\tgdmax\tband\n")
        for k, r, b in out_cells:
            g = r['geo']
            fh.write(f"{k}\t{g[0]}\t{g[1]}\t{r['alpha']:.6e}\t"
                     f"{r['TB']:.6e}\t{r['delta']:.3e}\t{r['Delta']:.3e}\t"
                     f"{r['cnorm']:.4e}\t{r['resid']:.1e}\t"
                     f"{r['F0'].real:.6e}\t{r['F0'].imag:.2e}\t"
                     f"{r['A']:.6e}\t{r['S']:.6e}\t{r['gdmax']:.2e}\t"
                     f"{b}\n")
    subprocess.run(["gzip", "-f", "docs/proofs/1403_rig_cells.tsv"],
                   check=True)
    for p in ("docs/proofs/1403_rig_results.json",
              "docs/proofs/1403_rig_cells.tsv.gz"):
        h = hashlib.sha256(open(p, 'rb').read()).hexdigest()
        print(f"sha256 {p} = {h}", flush=True)
    return 0


def _ser(r):
    d = dict(r)
    for k in ('F0', 'F0_npw24'):
        if k in d and isinstance(d[k], complex):
            d[k] = [d[k].real, d[k].imag]
    d['geo'] = list(r['geo'])
    return d


if __name__ == "__main__":
    sys.exit(main())
