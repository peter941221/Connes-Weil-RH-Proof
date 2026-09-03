"""1115 - exact-Q preprocessing for the rational-Cholesky (LDL^T)
ingestion brick. Pure stdlib Fractions; json bundles are the ONLY
inputs. Feasibility gate + Lean data source per
1115_rational_ingestion_preregistration.md. RH NOT claimed.
"""
import json
import os
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))


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
    """RREF-based exact nullspace; returns K (n x nullity, columns are
    the basis vectors)."""
    m, n = len(R), len(R[0])
    A = [row[:] for row in R]
    piv = []
    r = 0
    for c in range(n):
        pr = next((i for i in range(r, m) if A[i][c] != 0), None)
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        p = A[r][c]
        A[r] = [x / p for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == m:
            break
    assert r == m, f"rank {r} < {m}"
    free = [c for c in range(n) if c not in piv]
    K = []
    for fc in free:
        v = [F(0)] * n
        v[fc] = F(1)
        for i, pc in enumerate(piv):
            v[pc] = -A[i][fc]
        K.append(v)
    return mt(K)  # columns -> basis


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
            # inverse recurrence: sum over k in [j, i-1] (terms k<j vanish
            # only because Li[k][j]=0 for k<j, NOT because they're absent)
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


def load_classes():
    out = []
    for rec in ("1112_cert.json", "1113_cert.json"):
        b = json.load(open(os.path.join(HERE, rec)))
        for c in b["classes"]:
            if c["verdict"].startswith("PASS"):
                out.append((rec, c))
    return out


def render(x):
    return f"{float(x):.6e}"


results = []
for src, c in load_classes():
    A_R = c["A_R"]
    print(f"\n==== class ({A_R:g},8) from {src} - exact Q chain ====")
    n = 8
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
    U = frac(c["U_outward"][1])          # conservative upper
    R = [[frac(x) for x in row] for row in c["R_mid"]]
    assert all(len(row) == n for row in R)

    Drad = madd(mscale(abs(U), rad_G), rad_M)
    Dmid = msub(mscale(U, mid_G), mid_M)
    Dmid = [[(Dmid[i][j] + Dmid[j][i]) / 2 for j in range(n)]
            for i in range(n)]           # symmetrize exactly

    K = nullspace(R)                     # 8x5
    assert mm(R, K) == [[F(0)] * 5] * 3, "R*K != 0"
    RRt = mm(R, mt(R))
    dRR = det(RRt)
    assert dRR != 0, "R R^T singular"
    # exact 3x3 inverse of RR^T
    inv3 = [[(RRt[(i + 1) % 3][(j + 1) % 3] * RRt[(i + 2) % 3][(j + 2) % 3]
              - RRt[(i + 1) % 3][(j + 2) % 3] * RRt[(i + 2) % 3][(j + 1) % 3])
             for j in range(3)] for i in range(3)]
    inv3 = [[x / dRR for x in row] for row in inv3]
    W = mm(mt(R), inv3)                  # 8x3
    assert mm(R, W) == eye(3), "R*W != I"
    T = [row[:5] + [W[i][j] for j in range(3)] for i, row in enumerate(K)]
    dT = det(T)
    assert dT != 0, "T singular"

    Dred = mm(mt(K), mm(Dmid, K))        # 5x5
    Dred = [[(Dred[i][j] + Dred[j][i]) / 2 for j in range(5)]
            for i in range(5)]
    Dred_rad = mm(mabs(mt(K)), madd(mscale(abs(U), mabs(rad_G)),
                                    mabs(rad_M)))
    Dred_rad = mm(Dred_rad, mabs(K))
    # (|K|^T (U radG+radM) |K|) -- done above in one chain: verify shape
    assert len(Dred_rad) == 5 and len(Dred_rad[0]) == 5

    L, d = ldl(Dred)
    Lam = unit_lower_inv(L)
    Gp = mm(mt(Lam), mm(Dred, Lam))      # should be diag(d)
    assert all(Gp[i][j] == (d[i] if i == j else 0) for i in range(5)
               for j in range(5)), "congruence identity failed"
    radp = mm(mabs(Lam), mm(Dred_rad, mabs(mt(Lam))))
    slacks = []
    for i in range(5):
        s = Gp[i][i] - radp[i][i] - sum(
            abs(Gp[i][j]) + radp[i][j] for j in range(5) if j != i)
        slacks.append(s)
    print(f"U = {render(U)}   det(RR^T) = {render(dRR)}   "
          f"det(T) = {render(dT)}")
    print(f"LDL pivots d: {[render(x) for x in d]}")
    print(f"exact-Q DD slacks: {[render(s) for s in slacks]}")
    mn = min(slacks)
    print(f"min slack = {render(mn)}  ->  "
          f"{'GREEN (norm_num-able DD)' if mn > 0 else 'RED: falsifier - report only'}")

    if mn > 0:
        results.append(dict(src=src, A_R=A_R,
                            U=str(U),
                            mid_G=[[str(x) for x in r] for r in mid_G],
                            rad_G=[[str(x) for x in r] for r in rad_G],
                            mid_M=[[str(x) for x in r] for r in mid_M],
                            rad_M=[[str(x) for x in r] for r in rad_M],
                            R=[[str(x) for x in r] for r in R],
                            K=[[str(x) for x in r] for r in K],
                            W=[[str(x) for x in r] for r in W],
                            Ldl_L=[[str(x) for x in r] for r in L],
                            Ldl_d=[str(x) for x in d],
                            Lam=[[str(x) for x in r] for r in Lam],
                            Dred_rad=[[str(x) for x in r] for r in Dred_rad],
                            slacks=[str(s) for s in slacks],
                            min_slack_float=float(mn)))

out = json.dumps(dict(record="1115-qchain", classes=results), indent=1)
with open(os.path.join(HERE, "1115_qchain.json"), "w") as f:
    f.write(out)
print(f"\nwrote 1115_qchain.json with {len(results)} green classes")
print("DONE (exact-Q feasibility; Lean brick follows; RH NOT claimed)")
