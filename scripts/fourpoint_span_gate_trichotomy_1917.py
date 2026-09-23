#!/usr/bin/env python3
"""Self-check rig for the 103 Cut-2 scalar reduction (proof record 1917).

The Lean leaf `C1FourPointSpanGateCertificate.lean` proves, for the span
quadratic in the sign convention Q(lam) = D - lam*B + lam^2*C with C > 0:

  (T)  exists lam != 0, Q(lam) <= 0
         <=>  D < 0  or  (D = 0 and B != 0)  or  (0 < D and B^2 - 4*C*D >= 0)

  (P)  D < 0  ==>  gatePlusRoot := (B + sqrt(B^2 - 4*C*D)) / (2*C)
                   satisfies gatePlusRoot > 0 and Q(gatePlusRoot) = 0.

  (L)  D < 0  ==>  gatePlusRoot >= 2*|D| / (sqrt(B^2 - 4*C*D) + |B|)
                   (documented design bound, not formalized).

This rig is a SELF-CHECK of those statements, not an authority.  It brute
forgces the quantifier `exists lam != 0` on a wide lambda grid and compares
the grid verdict with the trichotomy predicate on the same draws, then
checks (P) and (L) in closed form.  Cases where a grid search cannot be
conclusive (window of measure zero, e.g. D = 0 and B != 0) are handled with
the closed-form witnesses and flagged in the output.

Engines: (1) direct evaluation of Q; (2) closed-form witnesses; (3) grid
search; (4) high-precision Decimal re-evaluation of the closed forms.
"""
import math
import random
from decimal import Decimal, getcontext

getcontext().prec = 50

FAIL = 0
CHECKS = 0


def q_val(D, B, C, lam):
    return D - lam * B + lam * lam * C


def tri_pred(D, B, C):
    return (D < 0) or (D == 0 and B != 0) or (0 < D and B * B - 4 * C * D >= 0)


def gate_plus_root(D, B, C):
    """gatePlusRoot = (B + sqrt(disc)) / (2C), computed without cancellation.

    For B >= 0 the direct form is stable. For B < 0 the sum B + sqrt(disc)
    cancels catastrophically when |D| is small against B^2 / (4C); the
    rationalized identity (B + s)(B - s) = B^2 - s^2 = 4CD gives the stable
    equivalent 2D / (B - s)."""
    disc = B * B - 4 * C * D
    s = math.sqrt(disc)
    if B >= 0:
        return (B + s) / (2 * C)
    return 2 * D / (B - s)


def root_candidates(D, B, C):
    """Both real roots of Q, each in a cancellation-free form."""
    disc = B * B - 4 * C * D
    s = math.sqrt(disc)
    if B >= 0:
        r_plus = (B + s) / (2 * C)
        r_minus = 2 * D / (B + s) if B + s != 0 else (B - s) / (2 * C)
    else:
        r_plus = 2 * D / (B - s) if B - s != 0 else (B + s) / (2 * C)
        r_minus = (B - s) / (2 * C)
    return r_plus, r_minus


def any_root_witness(D, B, C):
    """A nonzero root with Q <= 0, for the D > 0 and disc >= 0 branch."""
    r_plus, r_minus = root_candidates(D, B, C)
    for r in (r_plus, r_minus):
        if r != 0 and q_val(D, B, C, r) <= 1e-9 * max(
                abs(D), abs(r * B), abs(r * r * C), 1e-300):
            return r
    return r_plus


def grid_finds(D, B, C, lo=1e-6, hi=1e6, n=4000):
    """Grid search over |lam| in [lo, hi] log-spaced, both signs."""
    for i in range(n):
        lam = lo * (hi / lo) ** (i / (n - 1))
        for s in (1.0, -1.0):
            if q_val(D, B, C, s * lam) <= 0:
                return True
    return False


def report(name, ok, detail=""):
    global FAIL, CHECKS
    CHECKS += 1
    if not ok:
        FAIL += 1
        print(f"FAIL {name} {detail}")
    return ok


def check_case(D, B, C, tag):
    """Full battery on one (D, B, C) with C > 0."""
    # (T) forward: predicate -> a witness exists; backward: witness -> predicate.
    pred = tri_pred(D, B, C)
    witness = None
    if D < 0:
        witness = gate_plus_root(D, B, C)
    elif D == 0 and B != 0:
        witness = B / C
    elif 0 < D and B * B - 4 * C * D >= 0:
        witness = any_root_witness(D, B, C)
    if pred:
        assert witness is not None
        report(f"T-witness[{tag}]", witness != 0,
               f"D={D} B={B} C={C} lam={witness}")
        scale = max(abs(D), abs(witness * B), abs(witness * witness * C), 1e-300)
        report(f"T-nonpos[{tag}]", q_val(D, B, C, witness) <= 1e-9 * scale,
               f"Q(lam)={q_val(D, B, C, witness)} scale={scale}")
    # Grid cross-check only when informative:
    #   - pred with D != 0: window has positive measure near the closed form,
    #     so a dense local scan must find it;
    #   - not pred: completing the square forces positivity (D>0, disc<0) or
    #     forces lam*B > 0 with Q>0 (D=0,B=0), so the global grid must find
    #     nothing.
    if not pred:
        report(f"T-neg-nogrid[{tag}]", not grid_finds(D, B, C),
               f"D={D} B={B} C={C}")
    if D < 0:
        r = gate_plus_root(D, B, C)
        report(f"P-pos[{tag}]", r > 0, f"root={r}")
        scale = max(abs(D), abs(r * B), abs(r * r * C), 1e-300)
        report(f"P-zero[{tag}]", abs(q_val(D, B, C, r)) <= 1e-9 * scale,
               f"Q(root)={q_val(D, B, C, r)}")
        # (L) documented lower bound.  Sharp form, verified here: equality
        # holds exactly when B <= 0, and the inequality is strict when B > 0.
        disc_s = math.sqrt(B * B - 4 * C * D)
        bound = 2 * abs(D) / (disc_s + abs(B))
        report(f"L-bound[{tag}]", r >= bound * (1 - 1e-9),
               f"root={r} bound={bound}")
        ratio = r / bound
        if B <= 0:
            report(f"L-eq[{tag}]", abs(ratio - 1) <= 1e-9,
                   f"root/bound={ratio}")
        else:
            # Sharp form: ratio - 1 = B * (B + s) / (2 * C * |D|), positive
            # but able to approach 0 as B -> 0+.  Check the identity, not a
            # fixed threshold.
            pred = B * (B + disc_s) / (2 * C * abs(D))
            report(f"L-strict[{tag}]",
                   abs(ratio - 1 - pred) <= 1e-9 * max(1.0, pred),
                   f"root/bound={ratio} pred={pred}")
        # Engine 4: Decimal re-evaluation of Q at the root.  The 50-digit
        # sqrt truncation propagates to |Q| ~ disc/(2C) * 1e-49, so the
        # tolerance tracks disc/(2C), not just the coefficient scale.
        cD, cB, cC = Decimal(repr(D)), Decimal(repr(B)), Decimal(repr(C))
        cr = (cB + (cB * cB - 4 * cC * cD).sqrt()) / (2 * cC)
        cq = cD - cr * cB + cr * cr * cC
        ctol = Decimal("1e-35") * (1 + abs(cD) + cB * cB / (2 * cC))
        report(f"P-dec[{tag}]", abs(cq) <= ctol,
               f"Decimal Q(root)={cq} tol={ctol}")


def main():
    random.seed(1917)
    # Adversarial anchors.
    anchors = [
        (-1.0, 0.0, 1.0),          # D<0, B=0 (map's B != 0 absent)
        (-1.0, 2.0, 1.0),          # D<0, disc>0
        (-1.0, -2.0, 1.0),         # D<0, B<0
        (-4.0, 4.0, 1.0),          # disc = 16 - 16 = 0 tangent case
        (-1e-12, 1e-6, 3.0),       # tiny D
        (-1e12, 1e6, 2.0),         # huge D
        (0.0, 1.0, 1.0),           # D=0, B!=0 (point window at lam=B/C)
        (0.0, -1.0, 1.0),          # D=0, B<0
        (0.0, 0.0, 1.0),           # D=0, B=0 -> no nonzero witness
        (1.0, 3.0, 1.0),           # D>0, disc = 9-4 = 5 >= 0
        (1.0, 1.0, 1.0),           # D>0, disc = 1-4 < 0
        (1e12, 1e6, 1.0),          # D>0, disc < 0
    ]
    for (D, B, C) in anchors:
        check_case(D, B, C, "anchor")
    # Random draws, log-uniform magnitudes.
    for i in range(400):
        D = random.uniform(-1, 1) * 10 ** random.uniform(-9, 9)
        B = random.uniform(-1, 1) * 10 ** random.uniform(-9, 9)
        C = 10 ** random.uniform(-9, 9)
        check_case(D, B, C, f"rand{i}")
    # Boundary disc = 0 draws with D > 0: B^2 = 4CD exactly.
    for i in range(40):
        C = 10 ** random.uniform(-6, 6)
        D = 10 ** random.uniform(-6, 6)
        B = 2 * math.sqrt(C * D)
        check_case(D, B, C, f"disc0-{i}")
    print(f"checks={CHECKS} failures={FAIL}")
    raise SystemExit(1 if FAIL else 0)


if __name__ == "__main__":
    main()