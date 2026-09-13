# 1405 probe: Chuk arXiv:2608.24827 pillar-B dictionary -> cross-term test.
# Rev2: inv1's A-functional was reconstructed from the 1397 derivation and
# dropped the analytic tail term + the owner.Cg kink grid -> G0 FAIL ->
# invocation VOID (law 7j: artifacts renamed *.inv1.*, disclosed in 1406).
# The functional is now a VERBATIM transcription of run_1398_rig.compute_A
# with only the F call site substituted. Prereg file UNTOUCHED; gate
# classes UNCHANGED (law 42: this rev enforces the prereg's own section 4).
# ONE cell (tier-1 beta owner). Instruments imported VERBATIM from
# run_1403_rig (solve/owner/gd_lap) and run_1398_rig (_S_np, _panels,
# compute_A). Prereg: docs/proofs/1405_chuk_pillarB_bridge_recon_and_
# cross_term_probe_prereg.md sections 4-5. Model-level only (law 65).
# No Lean touched. RH not claimed.
import sys, os, time, json, math, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
import numpy as np
mp.mp.prec = 200
M, MC = mp.mpf, mp.mpc
import run_1398_rig as R
import run_1403_rig as B

RR, IM = B.TIER1
REF_A = M("-17.3431099115819")          # 1403 committed tier-1 A (G0 ref)
G0_TIE = M("2e-4"); G1_TIE = 1e-6
G2_TIE = M("1e-9"); G4_FIRE = M("1e-3")
LOG2 = M("0.6931471805599453094172321214581765680755001343602552541")
T0 = time.time()

def stamp(msg):
    print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)


# ---------------------------------------------------------------- owner data
fac = B.solve_factor7(B.nodes7(RR, IM), B.TARGETS)      # eps = EPS locked
own = B.SingleOwner(fac)
rOut = M(str(own.rOut)); d2 = M(str(own.d2))
modes = [mp.conj(MC(str(complex(n)))) for n in fac['nodes']]
coeffs = [MC(c) for c in fac['coeff'][:, 0]]

def S_mp(t):                                   # mirror of _S_np
    if t <= 0:
        return M(0)
    if t >= 1:
        return M(1)
    return mp.exp(-1 / t)

def h_mp(x):
    out = M(0)
    for c, md in zip(coeffs, modes):
        out += c * mp.exp(md * x)
    return S_mp((rOut - mp.fabs(x)) / d2) * out

def h_np(xs):
    return own.g(xs)                            # instrument evaluator

def r_np(xs):
    return own.g(xs).real

def m_np(xs):
    return own.g(xs).imag

# ------------------------------------------------- float autocorrelations
# u-grid for inner integrals: Gauss-Legendre per support-overlap interval
_GLX, _GLW = np.polynomial.legendre.leggauss(24)

def F_of(f1, f2, y, conj_first=True):
    """float64 int conj-ish f1(u - y) * f2(u) du over the support overlap."""
    a = max(-own.rOut, -own.rOut + y); b = min(own.rOut, own.rOut + y)
    if b <= a:
        return 0.0 + 0.0j
    acc = 0.0 + 0.0j
    n = max(1, int(np.ceil((b - a) / 0.05)))
    pts = list(np.linspace(a, b, n + 1))
    for l, h in zip(pts[:-1], pts[1:]):
        xs = 0.5 * (h - l) * _GLX + 0.5 * (h + l)
        w = 0.5 * (h - l) * _GLW
        acc += np.sum(w * (np.conj(f1(xs - y)) * f2(xs)))
    return acc

FC = np.complex128
def F_h(y):   return F_of(h_np, h_np, y)
def F_r(y):   return F_of(r_np, r_np, y)
def F_m(y):   return F_of(m_np, m_np, y)

def F_d(y):
    """cross part F_h - F_r - F_m (independent evaluator: direct mixed
    integrand conj(h(u-y))h(u) - r(u-y)r(u) - m(u-y)m(u))."""
    a = max(-own.rOut, -own.rOut + y); b = min(own.rOut, own.rOut + y)
    if b <= a:
        return 0.0 + 0.0j
    acc = 0.0 + 0.0j
    n = max(1, int(np.ceil((b - a) / 0.05)))
    pts = list(np.linspace(a, b, n + 1))
    for l, hh in zip(pts[:-1], pts[1:]):
        xs = 0.5 * (hh - l) * _GLX + 0.5 * (hh + l)
        w = 0.5 * (hh - l) * _GLW
        u_y = xs - y
        acc += np.sum(w * (np.conj(h_np(u_y)) * h_np(xs)
                           - r_np(u_y) * r_np(xs) - m_np(u_y) * m_np(xs)))
    return acc

# ------------------------------------------- arch functional: VERBATIM 1398
# Rev2 (disclosed 1406): inv1 violated this file's own prereg section 4
# ("No reimplementation of the ... A-functional") by reconstructing the
# functional from the 1397 paper derivation. The reconstruction dropped
# (i) the analytic tail term reF0 * log(tanh(Rg)) - the closed-form
# int_{2Rg}^inf of -2F0/(2 sinh y) beyond the support of F - and (ii) the
# owner.Cg kink grid, and integrated to 2*rOut instead of 2*Rg. G0 caught
# it (FAIL at 2.5e1), exactly the gate's purpose. The functions below are
# line-by-line transcriptions of run_1398_rig.compute_A; the ONLY edit is
# replacing the F_at(owner, y, npw) call site by an evaluator argument, so
# sector and cross autocorrelations pass through the same functional.
# A_float is the instrument's own float64 path; A_mp replicates its grid
# with 200-bit summation arithmetic (F values remain float64-sourced:
# G1 audits the summation class, not the integrand class).
def _agrid():
    """compute_A's breakpoint grid, verbatim."""
    Rg = own.Rg
    ks = set()
    for c1 in own.Cg:
        for c2 in own.Cg:
            for v in (abs(c1 + c2), abs(c1 - c2)):
                if 1e-9 < v < 2 * Rg:
                    ks.add(v)
    for c in own.Cg:
        if 1e-9 < abs(c) < 2 * Rg:
            ks.add(abs(c))
    ys = sorted(ks)
    ys = [0.0] + [y for y in ys if y > R.Y0] + [2.0 * Rg]
    if R.Y0 < 2 * Rg:
        ys = sorted(set(ys) | {R.Y0})
    freq = 2.0 * abs(np.imag(own.nodes[3])) + 2.0
    return Rg, freq, ys


def A_float(F):
    """compute_A float64, verbatim, with F evaluator substituted."""
    Rg, freq, ys = _agrid()
    F0 = complex(F(0.0))
    reF0 = F0.real
    integ = 0.0 + 0.0j
    for a, b in zip(ys[:-1], ys[1:]):
        xn, wn = R._panels([a, b], freq, R.NPW_DEFAULT)
        if xn.size == 0:
            continue
        Fy = np.array([complex(F(float(t))) for t in xn])
        num = np.exp(xn / 2) * 2 * np.real(Fy) - 2 * reF0
        den = np.exp(xn) - np.exp(-xn)
        integ += complex(np.sum(wn * num / den))
    A = complex(R.LOG4PI_G * F0 + integ
                + reF0 * math.log(math.tanh(Rg)))
    return float(A.real)


LOG4PI_G = M(str(R.LOG4PI_G))


def A_mp(F):
    """Same grid, 200-bit summation arithmetic."""
    Rg, freq, ys = _agrid()
    F0 = complex(F(0.0))
    reF0 = M(str(F0.real))
    mn = lambda v: M(str(float(v)))
    total = M(0)
    for a, b in zip(ys[:-1], ys[1:]):
        xn, wn = R._panels([a, b], freq, R.NPW_DEFAULT)
        if xn.size == 0:
            continue
        for t, w in zip(xn, wn):
            yt = mn(t)
            Fy = MC(F(float(t)))
            num = mp.exp(yt / 2) * 2 * mp.re(Fy) - 2 * reF0
            den = mp.exp(yt) - mp.exp(-yt)
            total += mn(w) * num / den
    tail = reF0 * mp.log(mp.tanh(mn(Rg)))
    return LOG4PI_G * reF0 + total + tail

# ------------------------------------------------------------ gates / run
def main():
    res = {}
    # committed-instrument cross-check (G0 + convention alignment)
    A1398, F01398, S1398 = R.compute_A(own)
    res['A_instrument'] = float(A1398)
    res['F0_instrument_re'] = float(np.real(F01398))
    res['probe_vs_instrument_F'] = [
        float(abs(complex(F_h(y)) - complex(R.F_at(own, y, 24))))
        for y in (0.0, 0.05, 0.2, 0.4, 0.55, 0.65)]
    A_h = A_float(F_h)
    res['A_h'] = str(A_h); res['A_h_f'] = float(A_h)
    res['G0'] = bool(abs(M(str(A_h)) - REF_A) <= G0_TIE)
    # per-quantity mp-vs-float summation agreement (G1)
    A_r = A_float(F_r); A_m = A_float(F_m); A_d = A_float(F_d)
    res.update({'A_r': str(A_r), 'A_m': str(A_m), 'A_d': str(A_d),
                'A_r_f': float(A_r), 'A_m_f': float(A_m), 'A_d_f': float(A_d)})
    res['A_mp_vs_float'] = [
        abs(A_mp(F) - M(str(A_float(F)))) / max(M(1), abs(M(str(A_float(F)))))
        for F in (F_h, F_r, F_m, F_d)]
    res['G1'] = float(max(res['A_mp_vs_float']))
    res['G1_ok'] = bool(res['G1'] <= G1_TIE)
    # inv1 forensics: split the VOID run's G0 gap (INV1_A_H from the
    # renamed artifact docs/proofs/1405_probe_results.inv1.json) into the
    # dropped analytic tail vs the grid/domain transcription residue.
    tail_term = complex(F_h(0.0)).real * math.log(math.tanh(own.Rg))
    res['forensic_tail_term'] = tail_term
    res['forensic_inv1_gap'] = -42.7645220321604053 - A_h
    res['forensic_grid_residue'] = res['forensic_inv1_gap'] - tail_term
    # poles: |lapAt h(+-1/2)|^2 sums (real/Hermitian tests), primes = 0
    Lp = B.gd_lap(own, complex(0.5)); Lm = B.gd_lap(own, complex(-0.5))
    res['pole_terms_max'] = float(abs(Lp) ** 2 + abs(Lm) ** 2)
    res['pole_ok'] = bool(res['pole_terms_max'] <= 1e-8)
    fp2 = float(abs(F_h(float(LOG2))))
    res['prime_probe_F_at_log2'] = fp2
    res['primes_ok'] = bool(fp2 <= 1e-16)
    # P values: psi = pole - arch - primes; poles/primes certified ~0
    P_h = -A_h; P_r = -A_r; P_m = -A_m; P_x = -A_d
    res.update({'P_h': float(P_h), 'P_r': float(P_r),
                'P_m': float(P_m), 'P_x': float(P_x)})
    # G2: identity P_h = P_r + P_m + P_x across INDEPENDENT evaluators
    res['G2'] = float(abs(P_h - P_r - P_m - P_x))
    res['G2_ok'] = bool(res['G2'] <= G2_TIE)
    # verdict
    if abs(P_x) >= G4_FIRE:
        vd = 'EXCLUDES_OWNER'
    elif abs(P_x) <= 1e-6:
        vd = 'COVERS_OWNER'
    else:
        vd = 'INCONCLUSIVE'
    res['VERDICT'] = vd
    ok = res['G0'] and res['G1_ok'] and res['G2_ok'] and \
        res['pole_ok'] and res['primes_ok']
    stamp(f"cell tier-1: A_h={float(A_h):+.13g} A_r={float(A_r):+.6g} "
          f"A_m={float(A_m):+.6g} A_d={float(A_d):+.6g}")
    stamp(f"P_h={float(P_h):+.13g} P_r={float(P_r):+.6g} "
          f"P_m={float(P_m):+.6g} P_x={float(P_x):+.6g} "
          f"G1={res['G1']:.2e} G2={res['G2']:.2e}")
    gates = ("DONE gates=" + ",".join(
        f"{k}:{'PASS' if v else 'FAIL'}" for k, v in
        [('G0', res['G0']), ('G1', res['G1_ok']), ('G2', res['G2_ok']),
         ('G4', ok and vd != 'INCONCLUSIVE')]))
    print(gates, flush=True)
    print(f"VERDICT chukBridge={vd} P_h={float(P_h):.13g} "
          f"P_r={float(P_r):.8g} P_m={float(P_m):.8g} P_x={float(P_x):.8g}",
          flush=True)
    path = os.path.join('docs', 'proofs', '1405_probe_results.json')
    with open(path, 'w') as fh:
        json.dump(res, fh, indent=1, sort_keys=True, default=str)
    with open(path, 'rb') as fh:
        print('sha256', path, '=', hashlib.sha256(fh.read()).hexdigest(),
              flush=True)
    stamp(f"done in {time.time()-T0:.1f}s")

if __name__ == "__main__":
    main()
