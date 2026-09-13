# 1407 dict cell: register psi(f~star f) vs Chuk Q(f) (arXiv:2608.24827
# eq 2 + raw-LaTeX Psi_L), one real even windowed test L = 1/2.
# Prereg: docs/proofs/1407_chuk_psi_Q_dictionary_double_evaluation_prereg.md
# sec 4-5. The archimedean functional is the VERBATIM compute_A
# transcription (F17) generalized to (evaluator, Rg, breaks); gate D0
# ties it to the committed tier-1 number BEFORE any dictionary digit.
# Model-level only (law 65). No Lean. RH not claimed.
# REV3 (rig-only, gate classes UNCHANGED, law-42 compliant): inv2 failed
# D1 at rel 1.74e-5 and the two pole paths at rel 1.76e-6; a quadrature
# diagnostic (mp 50-bit reference) showed R._panels' purely
# oscillation-density rule gives ONE 16-node GL panel to the flat bump on
# [0,L] (rel error: C 8.8e-7, fhat(11) 5.4e-6) while the register-side
# g_of was already accurate (identity check: register pole vs mp 2C^2
# agree to 3e-17 - no convention error). Fix: bump_edges() panels resolve
# BOTH amplitude (<=0.005) and half-period oscillation; and the
# TERM-DECOMP chuk prime/arch channels now print from the D1 t-integral
# (planch), not the y-side g_log2 substitution, so the decomposition is
# honest by construction.
import sys, os, time, json, math, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
import numpy as np
mp.mp.dps = 40
M, MC = mp.mpf, mp.mpc
import run_1398_rig as R
import run_1403_rig as B

L = 0.5
REF_A = M("-17.3431099115819")          # 1403 committed tier-1 A (D0 ref)
LOG2 = M("0.6931471805599453094172321214581765680755001343602552541")
D0_TIE = M("2e-4"); D1_TIE = 1e-8; D2_TIE = 1e-8; D3_TIE = 1e-14
T_CAP = 20000.0
T0 = time.time()


def stamp(msg):
    print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)


# ------------------------------------------------------------------ the test
def f_np(x):
    z = abs(x) / L
    return math.exp(-1.0 / (1.0 - z * z)) if z < 1.0 else 0.0


def f_np_v(xs):
    z = np.abs(xs) / L
    out = np.zeros_like(z)
    m = z < 1.0
    out[m] = np.exp(-1.0 / (1.0 - z[m] * z[m]))
    return out


# ------------------------------------------------- Chuk side (float64 path)
_GL16X, _GL16W = np.polynomial.legendre.leggauss(16)


def bump_edges(t):
    """Panel edges on [0,L] resolving BOTH the flat-bump amplitude
    (width <= 0.005; feature scale ~0.1 left the 1-panel rule at 1e-6)
    and the cos(t u) oscillation (half-period). REV3 rig fix, diagnostic
    above."""
    h = min(0.005, math.pi / max(abs(float(t)), 1.0))
    n = max(1, int(math.ceil(L / h)))
    return [i * L / n for i in range(n + 1)]


def fhat(t):
    """Fhat(t) = 2 int_0^L f(u) cos(tu) du, rev3 bump+oscillation panels."""
    xn, wn = R._panels(bump_edges(t), 0.0, 16)
    if xn.size == 0:
        return 0.0
    return 2.0 * float(np.sum(wn * f_np_v(xn) * np.cos(t * xn)))


def psi_symbol(t):
    """Psi_L(t) = Re digamma(1/4+it/2) - log pi - 2*(log2/sqrt2)cos(t log2)
    (raw main.tex eq, n=2 is the only comb term since log 3 > 2L)."""
    return (mp.re(mp.digamma(M(0.25) + MC(0, float(t) / 2)))
            - mp.log(mp.pi)
            - 2 * mp.log(M(2)) / mp.sqrt(M(2)) * mp.cos(M(str(float(t))) * LOG2))


_PSI_CACHE = {}


def psi_symbol_f(t):
    key = round(float(t), 12)
    v = _PSI_CACHE.get(key)
    if v is None:
        v = psi_symbol(t)
        _PSI_CACHE[key] = v
    return v


def q_chuk(mp_mode):
    """Q(f) = 2 Fhat(i/2)^2 + (1/pi) int_0^T Fhat^2 Psi_L, adaptive T
    with D3 tail audit. mp_mode: 200-bit summation on the same nodes."""
    xp, wp = R._panels(bump_edges(0.0), 0.0, 16)   # rev3: amplitude panels
    C = 2.0 * float(np.sum(wp * f_np_v(xp) * np.cosh(xp / 2.0)))
    pole = 2.0 * C * C
    T = 50.0
    info = {}
    while True:
        xn, wn = R._panels([0.0, T], 4.0, 32)          # t-grid
        Fv = np.array([fhat(t) for t in xn])
        Pv = np.array([float(psi_symbol_f(t)) for t in xn])
        if mp_mode:
            # same cached mp Psi values as the float path (dual-path D2
            # audits the SUMMATION arithmetic, not the special function)
            integ = sum((M(str(float(wn[i])))
                         * M(str(float(Fv[i]))) ** 2 * psi_symbol_f(xn[i])
                         for i in range(xn.size)), M(0))
        else:
            integ = float(np.sum(wn * Fv * Fv * Pv))
        q_partial = pole + integ / math.pi
        fT = fhat(T); pT = float(psi_symbol_f(T))
        tail = fT * fT * abs(pT) / max(1.0, abs(q_partial))
        info = dict(T=float(T), nodes=int(xn.size), tail_rel=float(tail),
                    pole=float(pole), pole_mp=float(pole),
                    C_fhat_i2=float(C))
        if tail <= D3_TIE or T >= T_CAP:
            break
        T *= 2.0
    if mp_mode:
        qv = M(str(pole)) + integ / M(str(math.pi))
        return qv, info
    return M(str(q_partial)), info


# ------------------------------------------------- register side (float64)
def g_of(y):
    """F(y) = (f~star f)(y) = int f(u-y) f(u) du, y >= 0 overlap (y-L, L)."""
    y = float(y)
    a, b = y - L, L
    if b - a < 1e-14:
        return 0.0
    n = max(1, int(np.ceil((b - a) / 0.02)))
    pts = np.linspace(a, b, n + 1)
    acc = 0.0
    for lo, hi in zip(pts[:-1], pts[1:]):
        xs = 0.5 * (hi - lo) * _GL16X + 0.5 * (hi + lo)
        ws = 0.5 * (hi - lo) * _GL16W
        acc += float(np.sum(ws * f_np_v(xs - y) * f_np_v(xs)))
    return acc


def A_gen(Feval, Rg, breaks):
    """VERBATIM run_1398_rig.compute_A with (evaluator, Rg, kink-breaks)
    generalized; float64.  F17: D0 must tie this to the committed
    tier-1 number on the owner path before any dictionary read."""
    F0 = complex(Feval(0.0))
    reF0 = F0.real
    freq = 4.0
    ks = set()
    for c1 in breaks:
        for c2 in breaks:
            for v in (abs(c1 + c2), abs(c1 - c2)):
                if 1e-9 < v < 2 * Rg:
                    ks.add(v)
    for c in breaks:
        if 1e-9 < abs(c) < 2 * Rg:
            ks.add(abs(c))
    ys = sorted(ks)
    ys = [0.0] + [y for y in ys if y > R.Y0] + [2.0 * Rg]
    if R.Y0 < 2 * Rg:
        ys = sorted(set(ys) | {R.Y0})
    integ = 0.0
    for a, b in zip(ys[:-1], ys[1:]):
        xn, wn = R._panels([a, b], freq, R.NPW_DEFAULT)
        if xn.size == 0:
            continue
        Fy = np.array([complex(Feval(float(t))).real for t in xn])
        num = np.exp(xn / 2) * 2 * Fy - 2 * reF0
        den = np.exp(xn) - np.exp(-xn)
        integ += float(np.sum(wn * num / den))
    return (R.LOG4PI_G * reF0 + integ
            + reF0 * math.log(math.tanh(Rg)))


def register_side():
    Rg = L
    arch = A_gen(g_of, Rg, [])
    pole = 4.0 * _quad1(lambda y: g_of(y) * math.cosh(y / 2.0), 0.0, 2 * Rg)
    primes = 2.0 * math.log(2.0) / math.sqrt(2.0) * g_of(float(LOG2))
    psi = pole - arch - primes
    return dict(arch=float(arch), pole=float(pole), primes=float(primes),
                psi=float(psi), g0=float(g_of(0.0)),
                g_log2=float(g_of(float(LOG2))))


def _quad1(fn, a, b):
    n = max(1, int(np.ceil((b - a) / 0.02)))
    pts = np.linspace(a, b, n + 1)
    acc = 0.0
    for lo, hi in zip(pts[:-1], pts[1:]):
        xs = 0.5 * (hi - lo) * _GL16X + 0.5 * (hi + lo)
        ws = 0.5 * (hi - lo) * _GL16W
        acc += float(np.sum(ws * np.array([fn(x) for x in xs])))
    return acc


# --------------------------------------------------------------- dual path
def dual_paths():
    """D2: float64 vs mp summation for psi parts and Q."""
    mn = lambda v: M(str(float(v)))
    # mp arch on the same float64-sourced nodes
    Rg = L
    g0 = M(str(g_of(0.0)))
    total = M(0)
    ys = [0.0, R.Y0, 2 * Rg]
    for a, b in zip(ys[:-1], ys[1:]):
        xn, wn = R._panels([a, b], 4.0, R.NPW_DEFAULT)
        for t, w in zip(xn, wn):
            yt = mn(t)
            num = mp.exp(yt / 2) * 2 * mn(g_of(float(t))) - 2 * g0
            total += mn(w) * num / (mp.exp(yt) - mp.exp(-yt))
    arch_mp = M(str(R.LOG4PI_G)) * g0 + total + g0 * mp.log(mp.tanh(mn(Rg)))
    pole_mp = 4 * M(str(_quad1(
        lambda y: g_of(y) * math.cosh(y / 2.0), 0.0, 2 * Rg)))
    primes_mp = 2 * mp.log(2) / mp.sqrt(2) * mn(g_of(float(LOG2)))
    psi_mp = pole_mp - arch_mp - primes_mp
    return dict(arch_mp=arch_mp, pole_mp=pole_mp, primes_mp=primes_mp,
                psi_mp=psi_mp)


# ------------------------------------------------------------------ run
def main():
    res = {}
    # ---- D0: generalized transcription ties committed tier-1 A
    fac = B.solve_factor7(B.nodes7(*B.TIER1), B.TARGETS)
    own = B.SingleOwner(fac)
    F_own = lambda y: R.F_at(own, y, R.NPW_DEFAULT)
    A_d0 = A_gen(F_own, own.Rg, [float(c) for c in own.Cg])
    res['D0_A_generalized'] = float(A_d0)
    res['D0_ref'] = float(REF_A)
    res['D0'] = bool(abs(M(str(A_d0)) - REF_A) <= D0_TIE)
    stamp(f"D0 generalized arch on tier-1 owner: {A_d0:+.13g} "
          f"vs committed {float(REF_A):+.13g} -> {'PASS' if res['D0'] else 'FAIL'}")
    if not res['D0']:
        print('DONE gates=D0:FAIL', flush=True)
        print('VERDICT dictPsiQ=BLOCKED_ON_D0', flush=True)
        return
    # ---- dictionary cell
    side = register_side()
    Qv, qinfo = q_chuk(mp_mode=False)
    res['chuk'] = qinfo
    res['chuk_Q'] = str(Qv); res['chuk_Q_f'] = float(Qv)
    res['register'] = side
    ratio = float(Qv) / side['psi'] if abs(side['psi']) > 1e-6 else None
    res['psi'] = side['psi']
    res['Q'] = float(Qv)
    # D1: Plancherel convention (their t-side primes channel = our y-side g)
    T = qinfo['T']
    xn, wn = R._panels([0.0, T], 4.0, 32)
    Fv = np.array([fhat(t) for t in xn])
    Cv = np.array([math.cos(float(t) * float(LOG2)) for t in xn])
    planch = float(np.sum(wn * Fv * Fv * Cv)) / math.pi
    res['D1_plancherel'] = dict(direct=planch, g_log2=side['g_log2'])
    d1 = abs(planch - side['g_log2']) / max(1e-30, abs(side['g_log2']))
    res['D1'] = bool(d1 <= D1_TIE)
    res['D1_rel'] = d1
    # D2: dual paths
    dp = dual_paths()
    Qv_mp, _info_mp = q_chuk(mp_mode=True)
    def rel(mp_v, f_v):
        return float(abs(mp_v - M(str(f_v))) / max(M(1), abs(M(str(f_v)))))
    res['D2_rel'] = dict(arch=rel(dp['arch_mp'], side['arch']),
                         psi=rel(dp['psi_mp'], side['psi']),
                         Q=rel(Qv_mp, float(Qv)))
    res['D2'] = bool(max(res['D2_rel'].values()) <= D2_TIE)
    # D3: tail audit already enforced in q_chuk; lock it
    res['D3'] = bool(qinfo['tail_rel'] <= float(D3_TIE) or qinfo['T'] < T_CAP
                     and qinfo['tail_rel'] <= float(D3_TIE))
    res['D3'] = bool(qinfo['tail_rel'] <= float(D3_TIE))
    # verdict
    if ratio is None:
        vd = 'DEGENERATE-TEST'; rv = 0.0
    else:
        rv = ratio
        scale = {'x2': 2.0, 'x4': 4.0, 'half': 0.5, 'quarter': 0.25,
                 'pi': math.pi, '2pi': 2 * math.pi,
                 '1/pi': 1 / math.pi, '1/2pi': 1 / (2 * math.pi)}
        if abs(rv - 1.0) <= 1e-6:
            vd = 'PLUS_ONE'
        elif abs(rv + 1.0) <= 1e-6:
            vd = 'MINUS_ONE'
        elif any(abs(rv - c) <= 1e-6 * abs(c) for c in scale.values()):
            vd = 'RESCALED:' + min(scale, key=lambda k: abs(rv - scale[k]))
        else:
            vd = 'OTHER'
    res['VERDICT'] = vd
    res['q_ratio'] = rv
    ok = res['D0'] and res['D1'] and res['D2'] and res['D3']
    print(f"DONE gates=" + ",".join(
        f"{k}:{'PASS' if v else 'FAIL'}" for k, v in
        [('D0', res['D0']), ('D1', res['D1']), ('D2', res['D2']),
         ('D3', res['D3'])]), flush=True)
    print(f"VERDICT dictPsiQ={vd} q_ratio={rv:.12g} psi={side['psi']:.12g} "
          f"Q={float(Qv):.12g}", flush=True)
    print("TERM-DECOMP register: pole=%.12g arch=%.12g primes=%.12g | "
          "chuk: pole=%.12g prime_channel=%.12g arch_channel=%.12g"
          % (side['pole'], side['arch'], side['primes'],
             qinfo['pole'], -(2 * math.log(2) / math.sqrt(2)) * planch,
             float(Qv) - qinfo['pole']
             + (2 * math.log(2) / math.sqrt(2)) * planch),
          flush=True)
    path = os.path.join('docs', 'proofs', '1407_dict_results.json')
    with open(path, 'w') as fh:
        json.dump(res, fh, indent=1, sort_keys=True, default=str)
    with open(path, 'rb') as fh:
        print('sha256', path, '=', hashlib.sha256(fh.read()).hexdigest(),
              flush=True)
    stamp(f"done in {time.time()-T0:.1f}s ok={ok}")


if __name__ == "__main__":
    main()
