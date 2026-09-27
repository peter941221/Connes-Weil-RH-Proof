#!/usr/bin/env python3
# routea_projection_inertia_exact_2045.py — record 2045 (exact rational checks)
#
# Interface lemmas for the D1 desk (neighbor-mechanism audit, arXiv 2608.13637).
# At the corrected-identity interface of record 016, with P a projection,
# H = 2P - 1, u unitary, P_hat = u^* (1 - P) u, T_S = u^* [H,u], and
# Q := u^* P u = 1 - P_hat:
#
#   L1  T_S = u^* H u - H = (1 - 2 P_hat) - (2P - 1) = 2 (Q - P)
#   L2  W_S(F) = -(1/2) Tr(theta_S(F) T_S) = Tr(theta_S(F) (P - Q))   [016 (6)]
#       => QW(g,g) = Tr(theta_S(F_g)(P - Q)) + Pole_lambda(g)         [016 (3)]
#                   = <theta_S(g), (P - Q) theta_S(g)> + Pole_lambda(g)
#   L3  A := P - Q.  The ENGINE identity (exact, one line):
#         (2Q - 1) A = 2QP - P - Q = -A (2P - 1),
#       equivalently the classical anti-identity (2P-1) A (2Q-1) = -A.
#       Consequently spec(A) = -spec(A): given Ax = lambda x with lambda != 0,
#       u0 := (2P-1)x and v0 := (2Q-1)x satisfy A u0 = -lambda v0 and
#       A v0 = -lambda u0, so A(u0+v0) = -lambda (u0+v0); and u0 + v0 = 0
#       implies (P+Q-1)x = 0, i.e. Px = (1+lambda)x/2 and Qx = (1-lambda)x/2,
#       so x ITSELF is a -lambda eigenvector of A.  Hence
#       A >= 0 <=> A = 0 <=> A <= 0 <=> [P,u] = 0.
#       A genuine semilocal phase has A indefinite with balanced +/- inertia:
#       NO operator-positivity mechanism can prove qw >= 0.
#       NOTE (recorded counterexample): the tempting identity u^* A u = -A is
#       FALSE in general (it holds iff u^2 commutes with P); the exact checks
#       below record it as false for t = 1/2 and true for t = 1.
#   L4  D(F) = (1/2) Tr(theta_S(F)(T_S - P T_S P)) = Tr(theta_S(F)(Q - P Q P));
#       with P = diag(1_k, 0) the block form is [[0, B],[B^T, C]],
#       B = Q[0:k, k:], C = Q[k:, k:]: indefinite iff B != 0
#       (iff [P, Q] != 0).  NO corner-sign mechanism can decide D.
#   L5  consistency: QW + D = Tr(theta_S(F_g) P P_hat P) = PositiveTrace >= 0,
#       and the record-016 (5) form of D coincides with the L4 form.
#
# All arithmetic is EXACT (fractions.Fraction); u is a rational orthogonal
# matrix (Pythagorean 2x2 rotation / rational unit quaternion 3x3 rotation),
# so every check is an identity, not a tolerance.

import json
import os
from fractions import Fraction as F
from itertools import combinations, product


def zeromat(n, m):
    return [[F(0)] * m for _ in range(n)]


def identity(n):
    return [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]


def transpose(A):
    return [list(row) for row in zip(*A)]


def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    C = zeromat(n, m)
    for i in range(n):
        Ci = C[i]
        Ai = A[i]
        for t in range(k):
            a = Ai[t]
            if a:
                Bt = B[t]
                for j in range(m):
                    Ci[j] += a * Bt[j]
    return C


def matadd(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def matsub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def scale(A, c):
    return [[c * x for x in row] for row in A]


def eq(A, B):
    return all(A[i][j] == B[i][j]
               for i in range(len(A)) for j in range(len(A[0])))


def trace(A):
    return sum(A[i][i] for i in range(len(A)))


def det(A):
    n = len(A)
    if n == 1:
        return A[0][0]
    if n == 2:
        return A[0][0] * A[1][1] - A[0][1] * A[1][0]
    a, b, c = A[0]
    d, e, f = A[1]
    g, h, i = A[2]
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def matpow(A, k):
    R = identity(len(A))
    for _ in range(k):
        R = matmul(R, A)
    return R


def rotation2(t):
    c = F(1 - t * t, 1 + t * t)
    s = F(2 * t, 1 + t * t)
    return [[c, -s], [s, c]]


def rotation3_from_quat(w, x, y, z):
    return [
        [1 - 2 * (y * y + z * z), 2 * (x * y - w * z), 2 * (x * z + w * y)],
        [2 * (x * y + w * z), 1 - 2 * (x * x + z * z), 2 * (y * z - w * x)],
        [2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x * x + y * y)],
    ]


def find_negative_witness(A, bound=12):
    n = len(A)
    for vec in product(range(-bound, bound + 1), repeat=n):
        if all(v == 0 for v in vec):
            continue
        x = [[F(v)] for v in vec]
        Ax = matmul(A, x)
        q = sum(x[i][0] * Ax[i][0] for i in range(n))
        if q < 0:
            return list(vec), str(q)
    return None, None


def is_psd_symmetric(A):
    n = len(A)
    if not eq(A, transpose(A)):
        return False
    for size in range(1, n + 1):
        for comb in combinations(range(n), size):
            sub = [[A[i][j] for j in comb] for i in comb]
            if det(sub) < 0:
                return False
    return True


def run_case(P, u, Theta, tag, eigen=None):
    """eigen: optional (x_col, lambda) rational eigenpair of A for the transfer check."""
    n = len(P)
    I = identity(n)
    res = {"tag": tag, "n": n}
    uT = transpose(u)
    res["u_orthogonal"] = eq(matmul(uT, u), I) and eq(matmul(u, uT), I)
    res["P_projection"] = eq(matmul(P, P), P) and eq(transpose(P), P)
    Phat = matmul(matmul(uT, matsub(I, P)), u)
    res["Phat_projection"] = (eq(matmul(Phat, Phat), Phat)
                              and eq(transpose(Phat), Phat))
    H = matsub(scale(P, 2), I)
    T = matsub(matmul(matmul(uT, H), u), H)
    Q = matmul(matmul(uT, P), u)
    res["Q_eq_1_minus_Phat"] = eq(Q, matsub(I, Phat))
    res["L1_T_eq_2(Q-P)"] = eq(T, scale(matsub(Q, P), 2))
    A = matsub(P, Q)
    twoP1 = matsub(scale(P, 2), I)
    twoQ1 = matsub(scale(Q, 2), I)
    res["L3_engine_conj_identity"] = eq(matmul(twoQ1, A),
                                        scale(matmul(A, twoP1), -1))
    res["L3_classical_anti_identity"] = eq(matmul(matmul(twoP1, A), twoQ1),
                                           scale(A, -1))
    res["L3_trace_zero"] = (trace(A) == 0)
    res["L3_trace_A3_zero"] = (trace(matpow(A, 3)) == 0)

    def charpoly_at(M, lam):
        return det(matsub(scale(identity(len(M)), lam), M))

    # spec(A) = -spec(A) <=> p(-lam) = (-1)^n p(lam) for the monic charpoly
    # p(lam) = det(lam I - A); four sample points pin a degree <= 3 difference.
    sign = F(-1) ** (n % 2)
    res["L3_charpoly_symmetric"] = all(
        charpoly_at(A, -lam) == sign * charpoly_at(A, lam)
        for lam in (F(1), F(2), F(3), F(4)))
    res["A_nonzero"] = not eq(A, zeromat(n, n))
    wit, q = find_negative_witness(A)
    res["L3_negative_witness"] = wit
    res["L3_negative_witness_value"] = q
    if not res["A_nonzero"]:
        # degenerate branch: A = 0 <=> [P,u] = 0; QW = D = PositiveTrace = 0
        res["L3_degenerate_u_commutes_P"] = eq(matmul(u, P), matmul(P, u))
        res["L3_degenerate_QW_zero"] = (trace(matmul(Theta, matsub(P, Q))) == 0)
    # recorded FALSE general claim: u^T A u = -A holds iff u^2 commutes with P
    res["L3_uT_A_u_eq_negA_general"] = eq(matmul(matmul(uT, A), u),
                                          scale(A, -1))
    res["L3_u2_P_commute"] = eq(matmul(matmul(u, u), P),
                                matmul(P, matmul(u, u)))
    if n == 2:
        res["L3_A2_scalar"] = eq(matmul(A, A),
                                 scale(I, trace(matmul(A, A)) / 2))
    if eigen is not None:
        x, lam = eigen
        Ax = matmul(A, x)
        ok1 = eq(Ax, scale(x, lam))
        u0 = matmul(twoP1, x)
        v0 = matmul(twoQ1, x)
        w = matadd(u0, v0)
        Aw = matmul(A, w)
        ok2 = (not eq(w, zeromat(n, 1))) and eq(Aw, scale(w, -lam))
        res["L3_eigen_transfer"] = {
            "lambda": str(lam), "Ax_eq_lam_x": ok1, "w": [str(r[0]) for r in w],
            "A_w_eq_minus_lam_w": ok2,
        }
    Qtilde = matsub(I, Phat)
    C4 = matsub(Qtilde, matmul(matmul(P, Qtilde), P))
    res["L4_defect_eq_Q_minus_PQP"] = eq(C4, matsub(Q, matmul(matmul(P, Q), P)))
    k = sum(1 for i in range(n) if P[i][i] == 1)
    if k < n:
        B = [row[k:] for row in Q[:k]]
        Cblk = [row[k:] for row in Q[k:]]
        target = zeromat(n, n)
        for i in range(k):
            for j in range(n - k):
                target[i][k + j] = B[i][j]
                target[k + j][i] = B[i][j]
        for i in range(n - k):
            for j in range(n - k):
                target[k + i][k + j] = Cblk[i][j]
        res["L4_block_form"] = eq(C4, target)
    res["Theta_psd"] = is_psd_symmetric(Theta)
    QWval = trace(matmul(Theta, matsub(P, Q)))
    Dval = trace(matmul(Theta, C4))
    PT = trace(matmul(Theta, matmul(matmul(P, Phat), P)))
    res["L5_QW_plus_D_eq_PositiveTrace"] = (QWval + Dval == PT)
    D16 = F(1, 2) * trace(matmul(Theta, matsub(T, matmul(matmul(P, T), P))))
    W16 = -F(1, 2) * trace(matmul(Theta, T))
    res["L5_D16_eq_Dval"] = (D16 == Dval)
    res["L5_W16_eq_QWval"] = (W16 == QWval)
    res["QW_value"] = str(QWval)
    res["D_value"] = str(Dval)
    res["PositiveTrace_value"] = str(PT)
    if tag == "2x2_t=1":
        res["A_matrix"] = [[str(x) for x in row] for row in A]
        res["C4_matrix"] = [[str(x) for x in row] for row in C4]
        res["Q_matrix"] = [[str(x) for x in row] for row in Q]
    return res


REQUIRED = ("u_orthogonal", "P_projection", "Phat_projection",
            "Q_eq_1_minus_Phat", "L1_T_eq_2(Q-P)",
            "L3_engine_conj_identity", "L3_classical_anti_identity",
            "L3_trace_zero", "L3_trace_A3_zero", "L3_charpoly_symmetric",
            "L4_defect_eq_Q_minus_PQP", "Theta_psd",
            "L5_QW_plus_D_eq_PositiveTrace", "L5_D16_eq_Dval",
            "L5_W16_eq_QWval")


def case_ok(c):
    if not all(c[key] for key in REQUIRED):
        return False
    if c["A_nonzero"]:
        return c["L3_negative_witness"] is not None
    return c["L3_degenerate_u_commutes_P"] and c["L3_degenerate_QW_zero"]


def main():
    cases = []
    two_by_two = [[F(2), F(1)], [F(1), F(2)]]           # PSD, eigenvalues 1,3
    three = [[F(3), F(1), F(0)], [F(1), F(3), F(1)], [F(0), F(1), F(3)]]
    for t in (F(1, 2), F(1), F(2)):
        eigen = None
        if t == F(1, 2):
            # A = (1/25)[[16,12],[12,-16]] has the rational eigenpair
            # x = (3,1), lambda = 4/5; transfer should produce w || x with -lambda
            eigen = ([[F(3)], [F(1)]], F(4, 5))
        cases.append(run_case(
            [[F(1), F(0)], [F(0), F(0)]], rotation2(t), two_by_two,
            "2x2_t=%s" % t, eigen=eigen))
    u3 = rotation3_from_quat(F(0), F(3, 5), F(4, 5), F(0))   # involution, axes
    cases.append(run_case(
        [[F(1), F(0), F(0)], [F(0), F(0), F(0)], [F(0), F(0), F(0)]],
        u3, three, "3x3_rank1"))
    cases.append(run_case(
        [[F(1), F(0), F(0)], [F(0), F(1), F(0)], [F(0), F(0), F(0)]],
        u3, three, "3x3_rank2_degenerate_A0"))
    u4 = rotation3_from_quat(F(3, 5), F(4, 5), F(0), F(0))   # rotation about e1
    cases.append(run_case(
        [[F(1), F(0), F(0)], [F(0), F(1), F(0)], [F(0), F(0), F(0)]],
        u4, three, "3x3_rank2_rotated"))
    all_ok = all(case_ok(c) for c in cases)
    fail_bits = [(c["tag"], key) for c in cases for key in REQUIRED
                 if not c[key]]
    out = {
        "record": 2045,
        "status": "PROJECTION-INERTIA-EXACT-PASS" if all_ok
                  else "PROJECTION-INERTIA-EXACT-FAIL",
        "note": ("exact rational verification of interface lemmas L1-L5 for the "
                 "corrected trace identity (record 016); toy matrices only, "
                 "algebra-level, no owner measurement, no RH claim.  The check "
                 "L3_uT_A_u_eq_negA_general is recorded as FALSE in general "
                 "(true iff u^2 commutes with P): the engine identity is "
                 "(2Q-1)A = -A(2P-1)."),
        "failed_checks": fail_bits,
        "cases": cases,
    }
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    path = os.path.join(root, "results", "2045_projection_inertia_exact.json")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print("STATUS", out["status"])
    for c in cases:
        print(c["tag"], "engine", c["L3_engine_conj_identity"],
              "classical", c["L3_classical_anti_identity"],
              "sym", c["L3_charpoly_symmetric"], "blk", c.get("L4_block_form"),
              "L5", c["L5_QW_plus_D_eq_PositiveTrace"],
              "utAu", c["L3_uT_A_u_eq_negA_general"],
              "negwit", c["L3_negative_witness"])
    print("RESULT", path)


if __name__ == "__main__":
    main()