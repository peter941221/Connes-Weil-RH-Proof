# 1405 probe: Chuk arXiv:2608.24827 pillar-B dictionary -> cross-term test.
# ONE cell (tier-1 beta owner). Instruments imported VERBATIM from
# run_1403_rig (solve/owner/gd_lap) and run_1398_rig (_S_np, _panels,
# compute_A). Prereg: docs/proofs/1405_chuk_pillarB_bridge_recon_and_
# cross_term_probe_prereg.md sections 4-5. Model-level only (law 65).
# No Lean touched. RH not claimed.
import sys, os, time, json, hashlib
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

# ------------------------------------------------------- generic arch (mp)
LOG4PI_G = mp.log(4 * mp.pi) + mp.euler

# mpmath 1.4.1 has no leggauss: float64 GL-24 nodes/weights (exact to
# ~1e-16, the panel error is far below every tie class since the F
# values feeding the integrand are float64-sourced anyway), lifted to
# mp for the arithmetic.
_glx, _glw = np.polynomial.legendre.leggauss(24)
_XG = [M(str(float(v))) for v in _glx]
_WG = [M(str(float(v))) for v in _glw]

def A_of(F, panels=32):
    """archimedeanTerm of a test F, FIXED mp Gauss-Legendre panels over
    float-sourced F values (adaptive mp.quad over float64 data spins:
    its 200-digit error controller chases 16-digit noise - inv2 stall).
    int_0^supp [e^{y/2}(F(y)+F(-y)) - 2F(0)]/(2 sinh y) dy; nodes are
    strictly interior, y = 0 never sampled."""
    F0 = complex(F(0.0))
    end = 2 * rOut
    total = M(0)
    half = end / panels
    for k in range(panels):
        a = end * M(k) / panels; b = a + half
        mid = (a + b) / 2
        for xi, wi in zip(_XG, _WG):
            y = half * xi + mid
            num = mp.re(mp.exp(y / 2) * (MC(F(y)) + MC(F(-y)))
                        - 2 * MC(F0))
            total += half * wi * num / (mp.e ** y - mp.e ** (-y))
    return LOG4PI_G * M(str(F0.real)) + total

def A_trapz(F):
    """float dense-grid mirror for G1."""
    end = 2 * own.rOut
    ys = np.linspace(1e-9, end, 131072)
    F0 = complex(F(0.0))
    Fy = np.array([F(y) for y in ys[:-1]])
    Fneg = np.array([F(-y) for y in ys[:-1]])
    g = np.real(np.exp(ys[:-1] / 2) * (Fy + Fneg) - 2 * F0) \
        / (2.0 * np.sinh(ys[:-1]))
    dy = np.diff(ys[:-1])
    integral = float(np.sum(0.5 * (g[:-1] + g[1:]) * dy))
    return float((np.log(4 * np.pi) + np.euler_gamma) * F0.real) + integral

# ------------------------------------------------------------ gates / run
def main():
    res = {}
    # committed-instrument cross-check (G0 + convention alignment)
    A1398, F01398, S1398 = R.compute_A(own)
    res['A_instrument'] = float(A1398)
    res['probe_vs_instrument_F'] = [
        float(abs(complex(F_h(y)) - complex(R.F_at(own, y, 24))))
        for y in (0.0, 0.05, 0.2, 0.4)]
    A_h = A_of(F_h)
    res['A_h'] = str(A_h); res['A_h_f'] = float(A_h)
    res['G0'] = bool(abs(A_h - REF_A) <= G0_TIE)
    # G1: mp-vs-float-mirror per quantity
    A_r = A_of(F_r); A_m = A_of(F_m); A_d = A_of(F_d)
    res.update({'A_r': str(A_r), 'A_m': str(A_m), 'A_d': str(A_d),
                'A_r_f': float(A_r), 'A_m_f': float(A_m), 'A_d_f': float(A_d)})
    res['G1'] = max(abs(float(A_h) - A_trapz(F_h)),
                    abs(float(A_r) - A_trapz(F_r)),
                    abs(float(A_m) - A_trapz(F_m)),
                    abs(float(A_d) - A_trapz(F_d))) \
        / max(1.0, abs(float(A_h)))
    res['G1_ok'] = bool(res['G1'] <= G1_TIE)
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
