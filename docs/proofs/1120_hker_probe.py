#!/usr/bin/env python3
"""Record 1120 probe: (c) Hker via C1 exact annihilation at span level.

Inputs (committed, read-only): docs/proofs/1115_qchain.json +
docs/proofs/1112_cert.json + docs/proofs/1113_cert.json.

All checks over exact Fractions.  Any FAIL => exit 1, no Lean emitted,
fall back to the 1118 C2 skeleton in a NEW preregistration (prereg
section 3).  RH NOT claimed.
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))

qchain = json.load(open(os.path.join(HERE, "1115_qchain.json")))["classes"]
cert1122 = json.load(open(os.path.join(HERE, "1112_cert.json")))["classes"]
cert113 = json.load(open(os.path.join(HERE, "1113_cert.json")))["classes"]
certs = cert1122 + cert113

CLASSES = [("q28", 2.0), ("q38", 3.0), ("q48", 4.0)]

ok_all = True


def check(name, ok, detail=""):
    global ok_all
    ok_all = ok_all and ok
    print(("PASS " if ok else "FAIL ") + name + (("  " + detail) if detail else ""))
    return ok


def mat_mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(m)) for j in range(p)]
            for i in range(n)]


def mat_T(A):
    return [list(r) for r in zip(*A)]


def det3(A):
    return (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
            - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
            + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))


digits = 0
for tag, ar in CLASSES:
    qc = next(c for c in qchain if c["A_R"] == ar)
    ce = next(c for c in certs if c["A_R"] == ar)
    R = [[F(x) for x in row] for row in qc["R"]]
    K = [[F(x) for x in row] for row in qc["K"]]
    A = [[F(x) for x in row] for row in qc["A_rref"]]
    E = [[F(x) for x in row] for row in qc["E_elim"]]
    piv, free = qc["pivots"], qc["free_cols"]

    # 0. R*K = 0 exact
    RK = mat_mul(R, K)
    check(f"[{tag}] 0. R*K = 0 exact", all(v == 0 for r in RK for v in r))

    # 1. rank(R) = 3: det(R R^T) != 0
    d = det3(mat_mul(R, mat_T(R)))
    check(f"[{tag}] 1. det(R R^T) != 0 (rank 3)", d != 0)

    # 2. lineage: qchain R == F(cert R_mid)
    Rm = [[F(x) for x in row] for row in ce["R_mid"]]
    check(f"[{tag}] 2. qchain R == F(cert R_mid)", R == Rm)

    # 3. K canonical: I_5 at free columns, pivot block = -A[:, free]
    canon = True
    for j, fc in enumerate(free):
        for i in range(8):
            want = F(1) if i == fc else F(0)
            if i in piv:
                want = -A[piv.index(i)][fc]
            if K[i][j] != want:
                canon = False
    check(f"[{tag}] 3. K = RREF nullspace basis (I_5 at free cols)",
          canon, f"pivots={piv} free={free}")

    # 4. full chain E*R = A_rref and A_rref*K = 0
    check(f"[{tag}] 4a. E*R = A_rref", mat_mul(E, R) == A)
    AK = mat_mul(A, K)
    check(f"[{tag}] 4b. A_rref*K = 0", all(v == 0 for r in AK for v in r))

    # 5. entry digit sizes
    dR = max(len(str(abs(v.numerator))) + len(str(v.denominator))
             for r in R for v in r)
    dK = max(len(str(abs(v.numerator))) + len(str(v.denominator))
             for r in K for v in r)
    digits = max(digits, dK)
    print(f"      [ {tag} entry digits: R {dR}, K {dK} ]")

print(f"\nmax K entry digits = {digits} (norm_num feasibility record)")
if not ok_all:
    print("\nFALSIFIER FIRED - C1 inapplicable; no Lean emitted; open a "
          "C2-skeleton preregistration per 1118 decision rule.")
    sys.exit(1)
print("ALL CHECKS PASS - C1 span closure verified on committed data")
