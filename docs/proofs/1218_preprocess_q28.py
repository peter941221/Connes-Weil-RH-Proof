"""1218 - exact-Q preprocessing for the consumption-chain regeneration
(prereg 1218_consumption_chain_regen_preregistration.md, committed
a51aa58 BEFORE this run; law 42).  Fork of
1115_rational_ingestion_preprocess.py: single class, bundle
1218_cert_q28.json, output 1218_qchain_q28.json.  All machinery is
byte-faithful to the committed fork parent; only the bundle path, the
class filter, and the regression gate are new.

REGRESSION GATE (prereg F3): mid_G / rad_G / R / K / V / W must be
BYTE-EQUAL to the committed 1115_qchain.json q28 entry - only the M
side may move.  Falsifier F4: min exact-Q slack <= 0 -> exit 2.

RH NOT claimed.
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
BUNDLE = os.path.join(HERE, "1218_cert_q28.json")
REF = os.path.join(HERE, "1115_qchain.json")
OUT = os.path.join(HERE, "1218_qchain_q28.json")


def mm(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m)]
            for i in range(n)]


def mt(A):
    return [list(r) for r in zip(*A)]


def mabs(A):
    return [[abs(x) for x in r] for r in A]


def madd(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))]
            for i in range(len(A))]


def msub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))]
            for i in range(len(A))]


def mscale(c, A):
    return [[c * x for x in r] for r in A]


def eye(n):
    return [[F(1 if i == j else 0) for j in range(n)] for i in range(n)]


def nullspace(R):
    """RREF-based exact nullspace; returns (K, A, E, piv, free)."""
    m, n = len(R), len(R[0])
    A = [row[:] for row in R]
    E = eye(m)
    piv = []
    r = 0
    for c in range(n):
        pr = next((i for i in range(r, m) if A[i][c] != 0), None)
        if pr is None:
            continue
        for row in (A, E):
            row[r], row[pr] = row[pr], row[r]
        p = A[r][c]
        A[r] = [x / p for x in A[r]]
        E[r] = [x / p for x in E[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
                E[i] = [a - f * b for a, b in zip(E[i], E[r])]
        piv.append(c)
        r += 1
        if r == m:
            break
    assert r == m, f"rank {r} < {m}"
    assert mm(E, R) == A, "E*R != A"
    free = [c for c in range(n) if c not in piv]
    K = []
    for fc in free:
        v = [F(0)] * n
        v[fc] = F(1)
        for i, pc in enumerate(piv):
            v[pc] = -A[i][fc]
        K.append(v)
    K = mt(K)
    assert mm(A, K) == [[F(0)] * len(free)] * m, "A*K != 0"
    return K, A, E, piv, free


def ldl(A):
    """Exact unit-LDL^T for symmetric A (no pivoting); returns (L, d)."""
    n = len(A)
    L = eye(n)
    d = []
    for j in range(n):
        s = A[j][j] - sum(L[j][k] * L[j][k] * d[k] for k in range(j))
        assert s > 0, f"non-positive pivot {j}: {float(s):.3e}"
        d.append(s)
        for i in range(j + 1, n):
            s2 = A[i][j] - sum(L[i][k] * L[j][k] * d[k] for k in range(j))
            L[i][j] = s2 / s
    return L, d


def unit_lower_inv(L):
    n = len(L)
    Li = eye(n)
    for i in range(n):
        for j in range(i):
            Li[i][j] = F(-sum(L[i][k] * Li[k][j] for k in range(j, i)))
    return Li


def det(A):
    n = len(A)
    M = [row[:] for row in A]
    s = F(1)
    for c in range(n):
        pr = next((i for i in range(c, n) if M[i][c] != 0), None)
        if pr is None:
            return F(0)
        if pr != c:
            M[c], M[pr] = M[pr], M[c]
            s = -s
        s *= M[c][c]
        p = M[c][c]
        for i in range(c + 1, n):
            f = M[i][c] / p
            M[i] = [a - f * b for a, b in zip(M[i], M[c])]
    return s


def frac(x):
    return F(x) if isinstance(x, str) else F(float(x))


def render(x):
    return f"{float(x):.6e}"


b = json.load(open(BUNDLE))
classes = [c for c in b["classes"] if c["verdict"].startswith("PASS")]
assert len(classes) == 1, f"expected 1 PASS class, got {len(classes)}"
c = classes[0]
src = "1218_cert_q28.json"
A_R = c["A_R"]
n = 8
print(f"==== class ({A_R:g},8) from {src} - exact Q chain (1218) ====")
mid_G = [[(frac(c["G_lo"][i][j]) + frac(c["G_hi"][i][j])) / 2
          for j in range(n)] for i in range(n)]
rad_G = [[(frac(c["G_hi"][i][j]) - frac(c["G_lo"][i][j])) / 2
          for j in range(n)] for i in range(n)]
mid_M = [[(frac(c["M_lo"][i][j]) + frac(c["M_hi"][i][j])) / 2
          for j in range(n)] for i in range(n)]
rad_M = [[(frac(c["M_hi"][i][j]) - frac(c["M_lo"][i][j])) / 2
          for j in range(n)] for i in range(n)]
for A in rad_G + rad_M:
    assert all(x >= 0 for x in A), "negative box radius"
U = frac(c["U_outward"][1])
R = [[frac(x) for x in row] for row in c["R_mid"]]
assert all(len(row) == n for row in R)

Drad = madd(mscale(abs(U), rad_G), rad_M)
Draw = msub(mscale(U, mid_G), mid_M)

# REGISTERED FINDING (1115 parent, verbatim): raw float-domain centers
# are not exactly symmetric; the T-center runs through the EXPLICIT
# symmetrization Dc := (Draw + Draw^T)/2.
asymG = max(abs(mid_G[i][j] - mid_G[j][i]) for i in range(n)
            for j in range(n))
asymM = max(abs(mid_M[i][j] - mid_M[j][i]) for i in range(n)
            for j in range(n))
asymD = max(abs(Draw[i][j] - Draw[j][i]) for i in range(n)
            for j in range(n))
print(f"raw-center asymmetry: G {float(asymG):.3e}  "
      f"M {float(asymM):.3e}  Draw {float(asymD):.3e}")
Dmid = [[(Draw[i][j] + Draw[j][i]) / 2 for j in range(n)] for i in range(n)]
assert Dmid == mt(Dmid), "symmetrization failed"

K, Arref, Elim, piv, free = nullspace(R)
assert mm(R, K) == [[F(0)] * 5] * 3, "R*K != 0"
RRt = mm(R, mt(R))
dRR = det(RRt)
assert dRR != 0, "R R^T singular"
inv3 = [[(RRt[(i + 1) % 3][(j + 1) % 3] * RRt[(i + 2) % 3][(j + 2) % 3]
          - RRt[(i + 1) % 3][(j + 2) % 3] * RRt[(i + 2) % 3][(j + 1) % 3])
         for j in range(3)] for i in range(3)]
inv3 = [[x / dRR for x in row] for row in inv3]
Wraw = mm(mt(R), inv3)
assert mm(R, Wraw) == eye(3), "R*Wraw != I"
V = [[F(1) if i == free[j] else F(0) for i in range(n)] for j in range(5)]
KV = mm(K, V)
Q = msub(eye(8), KV)
W = mm(Q, Wraw)
dT = det([r[:5] + [W[i][j] for j in range(3)]
          for i, r in enumerate(K)])
assert dT != 0, "T singular"
closure = madd(KV, mm(W, R))
assert closure == eye(8), "closure identity K*V + W*R = I FAILED"
print("kernel-closure identity K*V + W*R = I_8: EXACT")

Dred = mm(mt(K), mm(Dmid, K))
assert Dred == mt(Dred), "raw Dred = K^T Dc K not exactly symmetric"
Dred_rad = mm(mabs(mt(K)), madd(mscale(abs(U), mabs(rad_G)), mabs(rad_M)))
Dred_rad = mm(Dred_rad, mabs(K))
assert len(Dred_rad) == 5 and len(Dred_rad[0]) == 5

L, d = ldl(Dred)
Lam = unit_lower_inv(L)
Gp = mm(Lam, mm(Dred, mt(Lam)))
assert all(Gp[i][j] == (d[i] if i == j else 0) for i in range(5)
           for j in range(5)), "congruence identity failed"

diagd = [[d[i] if i == j else F(0) for j in range(5)] for i in range(5)]
assert mm(L, mm(diagd, mt(L))) == Dred, "L diag(d) L^T != Dred"
Dc = Dmid
DKc = mm(Dc, K)
KVc = KV
WRc = mm(W, R)
Ld = mm(L, diagd)
assert mm(mt(K), DKc) == Dred, "staged K^T (Dc K) != Dred"
assert madd(KVc, WRc) == eye(8), "staged KVc + WRc != I_8"
assert mm(Ld, mt(L)) == Dred, "staged (L diag) L^T != Dred"
radp = mm(mabs(Lam), mm(Dred_rad, mabs(mt(Lam))))
slacks = []
for i in range(5):
    s = Gp[i][i] - radp[i][i] - sum(
        abs(Gp[i][j]) + radp[i][j] for j in range(5) if j != i)
    slacks.append(s)
print(f"U = {render(U)}   det(RR^T) = {render(dRR)}   det(T) = {render(dT)}")
print(f"LDL pivots d: {[render(x) for x in d]}")
print(f"exact-Q DD slacks: {[render(s) for s in slacks]}")
mn = min(slacks)
print(f"min slack = {render(mn)}  ->  "
      f"{'GREEN (norm_num-able DD)' if mn > 0 else 'RED: falsifier F4'}")

# ---- prereg F3: regression gate vs the committed 1115 qchain q28 ----
ref = json.load(open(REF))
qc_ref = next(e for e in ref["classes"] if e["A_R"] == 2.0)
for field in ("mid_G", "rad_G", "R", "K", "V", "W"):
    if [[F(x) for x in row] for row in qc_ref[field]] != \
            [[F(x) for x in row] for row in
             (mid_G if field == "mid_G" else rad_G if field == "rad_G"
              else R if field == "R" else K if field == "K"
              else V if field == "V" else W)]:
        print(f"F3: G-side/kernel field {field} moved - must be identical")
        sys.exit(4)
print("F3 PASS: mid_G/rad_G/R/K/V/W byte-equal to committed 1115 q28 entry")

# prereg F4: feasibility
if mn <= 0:
    print(f"F4 FIRED: min slack = {render(mn)} <= 0 - ABORTED-UNINFORMATIVE")
    sys.exit(2)

Vinv = [[F(1) if i == free[j] else F(0) for i in range(n)] for j in range(5)]
assert mm(Vinv, K) == eye(5), "V*K != I"
result = dict(src=src, A_R=A_R,
              asym_G_float=float(asymG),
              asym_M_float=float(asymM),
              asym_D_float=float(asymD),
              U=str(U),
              mid_G=[[str(x) for x in r] for r in mid_G],
              rad_G=[[str(x) for x in r] for r in rad_G],
              mid_M=[[str(x) for x in r] for r in mid_M],
              rad_M=[[str(x) for x in r] for r in rad_M],
              R=[[str(x) for x in r] for r in R],
              K=[[str(x) for x in r] for r in K],
              V=[[str(x) for x in r] for r in Vinv],
              A_rref=[[str(x) for x in r] for r in Arref],
              E_elim=[[str(x) for x in r] for r in Elim],
              pivots=piv, free_cols=free,
              W=[[str(x) for x in r] for r in W],
              Draw=[[str(x) for x in r] for r in Draw],
              Dc=[[str(x) for x in r] for r in Dc],
              DKc=[[str(x) for x in r] for r in DKc],
              KVc=[[str(x) for x in r] for r in KVc],
              WRc=[[str(x) for x in r] for r in WRc],
              Ld=[[str(x) for x in r] for r in Ld],
              Dred=[[str(x) for x in r] for r in Dred],
              Ldl_L=[[str(x) for x in r] for r in L],
              Ldl_d=[str(x) for x in d],
              Lam=[[str(x) for x in r] for r in Lam],
              Dred_rad=[[str(x) for x in r] for r in Dred_rad],
              radp=[[str(x) for x in r] for r in radp],
              slacks=[str(s) for s in slacks],
              min_slack_float=float(mn))

out = json.dumps(dict(record="1218-qchain", classes=[result]), indent=1)
with open(OUT, "w") as f:
    f.write(out)
print(f"\nwrote 1218_qchain_q28.json (1 green class; RH NOT claimed)")
print("DONE (exact-Q feasibility on the TRUE boxes; RH NOT claimed)")
