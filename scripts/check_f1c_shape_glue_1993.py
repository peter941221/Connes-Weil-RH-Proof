#!/usr/bin/env python3
"""Record 1993 numeric pre-check for family brick F1c (shape bound + glue).

Validates, BEFORE the record is written (F27/F28 discipline — the Lean
brick C1GevreyFamilyGlue.lean is already proven; this rig checks that the
ENUNCIATED constants match the mathematics and measures tightness):

 1. SQUEEZE BOUND: |phi^(n)_k(u)| <= sqConst(n,k) * (1-u^2)^2 on
    k in {1, 3, 10, 30}, n in 0..8, interior grid — validity (ratio >= 1)
    and tightness (how many orders above the true derivative; feeds the
    F2 choose-n corollary).
    sqConst(n,k) = 5^n * n! * (2n+2)^(2n+2) / k^(n+2).
 2. BOUNDARY SLACK: 1 - (u+w)^2 <= 3|w| at u = +-1 (Lean-proved; the scan
    is a transcription guard).
 3. RECURSION PARITY: exact dict recursion B_{n+1} = B_n' + g' B_n vs
    mpmath.diff on phi at n in {1,2,4} (multiset-function check, mirrors
    record 1992's 1.3e-59).

Output: results/1993_f1c_shape_glue.json + PASS/FAIL summary to stdout.
"""

import json

import os
import sys

import mpmath as mp

mp.mp.dps = 50

K_VALUES = [1, 3, 10, 30]
N_MAX = 8
U_GRID = [mp.mpf(x) for x in
          ('0', '0.25', '0.5', '0.75', '0.9', '0.99', '0.999', '-0.5',
           '-0.9', '-0.99', '-0.999')]


def phi(k, u):
    """The committed window gevreyInner k u (float rep of the piecewise def)."""
    if abs(u) >= 1:
        return mp.mpf('0')
    return mp.e ** (-mp.mpf(k) / (1 - u * u))


def b_step(B):
    """One exact recursion step on the merged dict {(a, b, p): coef}.

    Product rule on c k^p u^a s^-b, the committed record-1990 form:
      u-move : a u^(a-1) s^-b          -> (a-1, b, p)   += c a
      s-move : 2b u^(a+1) s^-(b+1)     -> (a+1, b+1, p) += c 2b   (b >= 1)
      g-move : -2 k u^(a+1) s^-(b+2)   -> (a+1, b+2, p+1) += -2c  (k into p)
    """
    out = {}

    def add(key, val):
        out[key] = out.get(key, mp.mpf('0')) + val

    for (a, b, p), c in B.items():
        if a >= 1:
            add((a - 1, b, p), c * a)
        if b >= 1:
            add((a + 1, b + 1, p), c * 2 * b)
        add((a + 1, b + 2, p + 1), c * (-2))
    return {key: v for key, v in out.items() if v != 0}


def b_value(B, k, u):
    s = 1 - u * u
    tot = mp.mpf('0')
    for (a, b, p), c in B.items():
        tot += c * mp.mpf(k) ** p * u ** a * s ** (-b)
    return tot


def ladder(n):
    """Exact derivative ladder {(a,b,p): coef} for phi^(n) (merged dict;
    k enters only at evaluation, via the p-slot)."""
    B = {(0, 0, 0): mp.mpf(1)}
    for _ in range(n):
        B = b_step(B)
    return B


def sq_const(n, k):
    return (mp.mpf(5) ** n * mp.factorial(n)
            * mp.mpf(2 * n + 2) ** (2 * n + 2) / mp.mpf(k) ** (n + 2))


def main():
    verdict = {"check1_bound": [], "check2_slack": {}, "check3_parity": []}
    all_pass = True

    # -- Check 1: squeeze bound dominates; measure tightness ----------------
    worst_ratio = None
    best_ratio = None
    for k in K_VALUES:
        ladders = {}
        for n in range(N_MAX + 1):
            ladders[n] = ladder(n)
        for n in range(N_MAX + 1):
            C = sq_const(n, k)
            for u in U_GRID:
                s = 1 - u * u
                true = abs(mp.e ** (-mp.mpf(k) / s)
                           * b_value(ladders[n], k, u))
                bound = C * s * s
                ratio = bound / true if true > 0 else mp.mpf('inf')
                if n == 0 and u == 0:
                    pass  # phi(0)=e^{-k} > 0, fine
                row = {"k": k, "n": n, "u": mp.nstr(u, 6),
                       "true": mp.nstr(true, 6), "bound": mp.nstr(bound, 6),
                       "ratio": mp.nstr(ratio, 6)}
                verdict["check1_bound"].append(row)
                if ratio < 1:
                    all_pass = False
                    row["FAIL"] = True
                if worst_ratio is None or ratio < worst_ratio:
                    worst_ratio = ratio
                if best_ratio is None or ratio > best_ratio:
                    best_ratio = ratio
    verdict["check1_summary"] = {
        "rows": len(verdict["check1_bound"]),
        "min_ratio": mp.nstr(worst_ratio, 8),
        "max_ratio": mp.nstr(best_ratio, 8),
        "pass": all_pass,
    }

    # -- Check 2: boundary slack 1-(u+w)^2 <= 3|w| at u = +-1 ----------------
    slack_ok = True
    slack_max = mp.mpf('0')
    for u0 in (mp.mpf(1), mp.mpf(-1)):
        for i in range(-400, 1):
            w = mp.mpf(i) / 400  # w < 0 for u=1; need also w > 0 for u=-1
            if u0 == -1:
                w = -w
            if abs(u0 + w) >= 1:
                continue
            lhs = 1 - (u0 + w) ** 2
            rhs = 3 * abs(w)
            q = lhs / rhs if rhs > 0 else mp.mpf('0')
            if q > slack_max:
                slack_max = q
            if lhs > rhs + mp.mpf('1e-40'):
                slack_ok = False
    verdict["check2_slack"] = {
        "max_lhs_over_3absw": mp.nstr(slack_max, 8),
        "pass": slack_ok,
    }
    all_pass = all_pass and slack_ok

    # -- Check 3: recursion parity vs mpmath.diff ----------------------------
    parity_ok = True
    for k in (1, 10):
        for n in (1, 2, 4):
            B = ladder(n)
            for u in (mp.mpf('0.3'), mp.mpf('-0.8'), mp.mpf('0.95')):
                true = mp.e ** (-mp.mpf(k) / (1 - u * u)) * b_value(B, k, u)
                num = mp.diff(lambda x: phi(k, x), u, n)
                mag = abs(true) + mp.mpf('1e-60')
                rel = abs(true - num) / mag
                row = {"k": k, "n": n, "u": mp.nstr(u, 4),
                       "rel": mp.nstr(rel, 4)}
                if rel > mp.mpf('1e-25'):
                    parity_ok = False
                    row["FAIL"] = True
                verdict["check3_parity"].append(row)
    verdict["check3_summary"] = {"pass": parity_ok}
    all_pass = all_pass and parity_ok

    verdict["overall_pass"] = all_pass

    out = os.path.join(os.path.dirname(__file__), "..", "results",
                       "1993_f1c_shape_glue.json")
    out = os.path.abspath(out)
    with open(out, "w") as f:
        json.dump(verdict, f, indent=1)
    print(f"wrote {out}")
    print(f"check1 bound: {len(verdict['check1_bound'])} rows, "
          f"min ratio {verdict['check1_summary']['min_ratio']}, "
          f"max ratio {verdict['check1_summary']['max_ratio']}, "
          f"pass={verdict['check1_summary']['pass']}")
    print(f"check2 slack: max(1-(u+w)^2)/(3|w|) = "
          f"{verdict['check2_slack']['max_lhs_over_3absw']}, "
          f"pass={verdict['check2_slack']['pass']}")
    print(f"check3 parity: pass={verdict['check3_summary']['pass']}")
    print(f"OVERALL: {'PASS' if all_pass else 'FAIL'}")
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
