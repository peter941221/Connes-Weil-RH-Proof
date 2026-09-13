# 1410 odd-sector dictionary cell: register psi(f_o~star f_o) vs Chuk Q(f_o),
# f_o odd C-infinity bump, L = 1/2. Prereg:
# docs/proofs/1410_odd_sector_dictionary_cell_prereg.md sec 3-5. Reuses the
# 1407 rev3 machinery by import (A_gen verbatim transcription + D0 tie kept
# as O0; psi symbol; panels); ONLY the bump is odd. g_o inner amplitude
# panel cap 0.0025 (disclosed prereg sec 3; quadrature only, gate classes
# unchanged). Model-level only (law 65). No Lean. RH not claimed.
import sys, os, time, json, math, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
import numpy as np
mp.mp.dps = 40
M, MC = mp.mpf, mp.mpc
import run_1398_rig as R
import run_1403_rig as B
import run_1407_dict as D

L = 0.5
T0 = time.time()


def stamp(msg):
    print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)


# ------------------------------------------------------------------ the odd test
def fo_np(x):
    z = abs(x) / L
    return (x / L) * math.exp(-1.0 / (1.0 - z * z)) if z < 1.0 else 0.0


def fo_np_v(xs):
    z = np.abs(xs) / L
    out = np.zeros_like(z)
    m = z < 1.0
    out[m] = (xs[m] / L) * np.exp(-1.0 / (1.0 - z[m] * z[m]))
    return out


# ------------------------------------------------- Chuk side (float64 path)
def fhatO(t):
    """|Fhat_o(t)|: Fhat_o = i * 2 int_0^L f_o(u) sin(tu) du (odd real f)."""
    xn, wn = R._panels(D.bump_edges(t), 0.0, 16)
    if xn.size == 0:
        return 0.0
    return 2.0 * float(np.sum(wn * fo_np_v(xn) * np.sin(t * xn)))


def pole_odd_mp():
    """-2 C(1/2)^2, C(1/2) = int_R f_o sinh(y/2) dy = 2 int_0^L f_o sinh."""
    xp, wp = R._panels(D.bump_edges(0.0), 0.0, 16)
    S = 2.0 * float(np.sum(wp * fo_np_v(xp) * np.sinh(xp / 2.0)))
    return -2.0 * S * S


def q_o(mp_mode):
    """Q_o = -2C(1/2)^2 + (1/pi) int_0^T fhatO^2 Psi_L, adaptive T, D3-class
    tail. Same locked symbol + panel rule as 1407 rev3."""
    pole = pole_odd_mp()
    T = 50.0
    info = {}
    while True:
        xn, wn = R._panels([0.0, T], 4.0, 32)
        Fv = np.array([fhatO(t) for t in xn])
        Pv = np.array([float(D.psi_symbol_f(t)) for t in xn])
        if mp_mode:
            integ = sum((M(str(float(wn[i])))
                         * M(str(float(Fv[i]))) ** 2 * D.psi_symbol_f(xn[i])
                         for i in range(xn.size)), M(0))
        else:
            integ = float(np.sum(wn * Fv * Fv * Pv))
        q_partial = pole + integ / math.pi
        fT = fhatO(T); pT = float(D.psi_symbol_f(T))
        tail = fT * fT * abs(pT) / max(1.0, abs(q_partial))
        info = dict(T=float(T), nodes=int(xn.size), tail_rel=float(tail),
                    pole=float(pole))
        if tail <= D.D3_TIE or T >= D.T_CAP:
            break
        T *= 2.0
    if mp_mode:
        return M(str(pole)) + integ / M(str(math.pi)), info
    return M(str(q_partial)), info


# ------------------------------------------------- register side (float64)
_G16X, _G16W = np.polynomial.legendre.leggauss(16)


def g_o_of(y):
    """F_o(y) = (f_o~star f_o)(y) = int f_o(v-y) f_o(v) dv, even in y;
    amplitude panel cap 0.0025 (prereg sec 3)."""
    y = float(y)
    a, b = y - L, L
    if b - a < 1e-14:
        return 0.0
    n = max(1, int(np.ceil((b - a) / 0.0025)))
    pts = np.linspace(a, b, n + 1)
    acc = 0.0
    for lo, hi in zip(pts[:-1], pts[1:]):
        xs = 0.5 * (hi - lo) * _G16X + 0.5 * (hi + lo)
        ws = 0.5 * (hi - lo) * _G16W
        acc += float(np.sum(ws * fo_np_v(xs - y) * fo_np_v(xs)))
    return acc


def register_side_odd():
    Rg = L
    arch = D.A_gen(g_o_of, Rg, [])
    pole = 4.0 * D._quad1(lambda y: g_o_of(y) * math.cosh(y / 2.0),
                          0.0, 2 * Rg)
    primes = 2.0 * math.log(2.0) / math.sqrt(2.0) * g_o_of(float(D.LOG2))
    psi = pole - arch - primes
    return dict(arch=float(arch), pole=float(pole), primes=float(primes),
                psi=float(psi), g0=float(g_o_of(0.0)),
                g_log2=float(g_o_of(float(D.LOG2))))


def dual_paths_odd(side):
    """O2: mp summation on the same float64-sourced node values."""
    mn = lambda v: M(str(float(v)))
    Rg = L
    g0 = mn(g_o_of(0.0))
    total = M(0)
    for a, b in [(0.0, R.Y0), (R.Y0, 2 * Rg)]:
        xn, wn = R._panels([a, b], 4.0, R.NPW_DEFAULT)
        for t, w in zip(xn, wn):
            yt = mn(t)
            num = mp.exp(yt / 2) * 2 * mn(g_o_of(float(t))) - 2 * g0
            total += mn(w) * num / (mp.exp(yt) - mp.exp(-yt))
    arch_mp = M(str(R.LOG4PI_G)) * g0 + total + g0 * mp.log(mp.tanh(mn(Rg)))
    pole_mp = 4 * M(str(D._quad1(
        lambda y: g_o_of(y) * math.cosh(y / 2.0), 0.0, 2 * Rg)))
    primes_mp = 2 * mp.log(2) / mp.sqrt(2) * mn(g_o_of(float(D.LOG2)))
    psi_mp = pole_mp - arch_mp - primes_mp
    return dict(arch_mp=arch_mp, pole_mp=pole_mp, primes_mp=primes_mp,
                psi_mp=psi_mp)


# ------------------------------------------------------------------ run
def main():
    res = {}
    # ---- O0: shared transcription still ties committed tier-1 A
    fac = B.solve_factor7(B.nodes7(*B.TIER1), B.TARGETS)
    own = B.SingleOwner(fac)
    F_own = lambda y: R.F_at(own, y, R.NPW_DEFAULT)
    A_o0 = D.A_gen(F_own, own.Rg, [float(c) for c in own.Cg])
    res['O0_A_generalized'] = float(A_o0)
    res['O0_ref'] = float(D.REF_A)
    res['O0'] = bool(abs(M(str(A_o0)) - D.REF_A) <= D.D0_TIE)
    stamp(f"O0 generalized arch on tier-1 owner: {A_o0:+.13g} "
          f"vs committed {float(D.REF_A):+.13g} -> "
          f"{'PASS' if res['O0'] else 'FAIL'}")
    if not res['O0']:
        print('DONE gates=O0:FAIL', flush=True)
        print('VERDICT dictPsiQodd=BLOCKED_ON_O0', flush=True)
        return
    # ---- odd dictionary cell
    side = register_side_odd()
    Qo, oinfo = q_o(mp_mode=False)
    res['chuk_odd'] = oinfo
    res['Q_o'] = float(Qo)
    res['register_odd'] = side
    res['psi_o'] = side['psi']
    ratio = float(Qo) / side['psi'] if abs(side['psi']) > 1e-6 else None
    # O1: odd Plancherel convention (t-side vs y-side g_o(log2))
    T = oinfo['T']
    xn, wn = R._panels([0.0, T], 4.0, 32)
    Fv = np.array([fhatO(t) for t in xn])
    Cv = np.array([math.cos(float(t) * float(D.LOG2)) for t in xn])
    planch = float(np.sum(wn * Fv * Fv * Cv)) / math.pi
    res['O1_plancherel'] = dict(direct=planch, g_log2=side['g_log2'])
    o1 = abs(planch - side['g_log2']) / max(1e-30, abs(side['g_log2']))
    res['O1'] = bool(o1 <= D.D1_TIE)
    res['O1_rel'] = o1
    # O2 dual paths
    dp = dual_paths_odd(side)
    Qo_mp, _info = q_o(mp_mode=True)

    def rel(mp_v, f_v):
        return float(abs(mp_v - M(str(f_v))) / max(M(1), abs(M(str(f_v)))))
    res['O2_rel'] = dict(arch=rel(dp['arch_mp'], side['arch']),
                         psi=rel(dp['psi_mp'], side['psi']),
                         Q=rel(Qo_mp, float(Qo)))
    res['O2'] = bool(max(res['O2_rel'].values()) <= D.D2_TIE)
    # O3 tail class
    res['O3'] = bool(oinfo['tail_rel'] <= float(D.D3_TIE))
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
    print("DONE gates=" + ",".join(
        f"{k}:{'PASS' if v else 'FAIL'}" for k, v in
        [('O0', res['O0']), ('O1', res['O1']), ('O2', res['O2']),
         ('O3', res['O3'])]), flush=True)
    print(f"VERDICT dictPsiQodd={vd} q_ratio={rv:.12g} psi={side['psi']:.12g}"
          f" Q={float(Qo):.12g}", flush=True)
    print("TERM-DECOMP register: pole=%.12g arch=%.12g primes=%.12g | "
          "chuk: pole=%.12g prime_channel=%.12g arch_channel=%.12g"
          % (side['pole'], side['arch'], side['primes'],
             oinfo['pole'], -(2 * math.log(2) / math.sqrt(2)) * planch,
             float(Qo) - oinfo['pole']
             + (2 * math.log(2) / math.sqrt(2)) * planch), flush=True)
    path = os.path.join('docs', 'proofs', '1410_odict_results.json')
    with open(path, 'w') as fh:
        json.dump(res, fh, indent=1, sort_keys=True, default=str)
    with open(path, 'rb') as fh:
        print('sha256', path, '=', hashlib.sha256(fh.read()).hexdigest(),
              flush=True)
    stamp(f"done in {time.time()-T0:.1f}s")


if __name__ == "__main__":
    main()
