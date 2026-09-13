# Rig diagnostic (no verdict numbers): does 1-panel GL-16 resolution of the
# flat bump explain inv2's D1 rel=1.74e-5 and pole-path rel=1.76e-6?
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, mpmath as mp
mp.mp.dps = 50
M = mp.mpf
import run_1398_rig as R
import run_1407_dict as D
L = 0.5
LOG2v = 0.6931471805599453


def f_np(x):
    z = abs(x) / L
    return math.exp(-1.0 / (1.0 - z * z)) if z < 1.0 else 0.0


def f_mp(x):
    z = abs(x) / L
    return mp.e ** (-1 / (1 - z * z)) if z < 1 else mp.mpf(0)


_GX, _GW = np.polynomial.legendre.leggauss(16)


def dense_int(g, a, b, h=0.005):
    n = max(1, int(math.ceil((b - a) / h)))
    pts = np.linspace(a, b, n + 1)
    acc = 0.0
    for lo, hi in zip(pts[:-1], pts[1:]):
        xs = 0.5 * (hi - lo) * _GX + 0.5 * (hi + lo)
        ws = 0.5 * (hi - lo) * _GW
        acc += float(np.sum(ws * np.array([g(x) for x in xs])))
    return acc


# 1) C = 2 int_0^L f(x) cosh(x/2) dx : 1-panel vs dense vs mp
xp, wp = R._panels([0.0, L], 3.0, 16)
C1 = 2.0 * float(np.sum(wp * np.array([f_np(x) for x in xp]) * np.cosh(xp / 2)))
Cd = 2.0 * dense_int(lambda x: f_np(x) * math.cosh(x / 2), 0.0, L)
Cm = float(2.0 * mp.quad(lambda x: f_mp(x) * mp.cosh(x / 2), [0, L]))
print('C: 1panel %.16g  dense %.16g  mp %.16g' % (C1, Cd, Cm))
print('   rel 1p-vs-mp %.3g   dense-vs-mp %.3g'
      % (abs(C1 - Cm) / Cm, abs(Cd - Cm) / Cm))

# 2) fhat(t): 1-panel (current) vs dense vs mp
def fhat1(t):
    xn, wn = R._panels([0.0, L], float(abs(t)) + 1.0, 16)
    if xn.size == 0:
        return 0.0
    return 2.0 * float(np.sum(wn * np.array([f_np(x) for x in xn]) * np.cos(t * xn)))


def fhatD(t):
    h = min(0.005, math.pi / max(abs(float(t)), 1.0))
    n = max(1, int(math.ceil(L / h)))
    edges = [i * L / n for i in range(n + 1)]
    xn, wn = R._panels(edges, 0.0, 16)
    return 2.0 * float(np.sum(wn * f_np_v(xn) * np.cos(t * xn)))


def f_np_v(xs):
    z = np.abs(xs) / L
    out = np.zeros_like(z)
    m = z < 1.0
    out[m] = np.exp(-1.0 / (1.0 - z[m] * z[m]))
    return out


for t in (0.0, 1.0, 3.0, 11.0):
    a, b = fhat1(t), fhatD(t)
    c = float(2.0 * mp.quad(lambda x: f_mp(x) * mp.cos(x * t), [0, L]))
    print('fhat(%3g): 1p %.14g dense %.14g mp %.14g | rel1p %.2g reld %.2g'
          % (t, a, b, c, abs(a - c) / max(1e-30, abs(c)),
             abs(b - c) / max(1e-30, abs(c))))

# 3) g_of (current 0.02 subpanels) vs dense 0.004
for y in (0.0, LOG2v, 0.95):
    print('g(%.4f): cur %.14g dense %.14g' % (y, D.g_of(y),
          dense_int(lambda v: f_np(v - y) * f_np(v), y - L, L, 0.004)))

# 4) register pole (4 int_0^{2L} g cosh) current-g vs dense-g; chuk 2C^2 mp
p1 = 4 * dense_int(lambda y: D.g_of(y) * math.cosh(y / 2), 0.0, 1.0, 0.01)
p2 = 4 * dense_int(lambda y: dense_int(lambda v: f_np(v - y) * f_np(v),
                                       y - L, L, 0.004) * math.cosh(y / 2),
                   0.0, 1.0, 0.01)
print('pole cur-g %.16g  dense-g %.16g  chuk-2C2(mp) %.16g'
      % (p1, p2, 2 * Cm * Cm))
