# M.2 boundary scan (990): locate the healthy-psi sign boundary in the
# two-sided window (lo, hi) of the finite-vanishing test family (989).
# Imports one_case from 989 (single source of truth).
# Numeric evidence only. RH NOT claimed.
import importlib.util
import os
import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "p989one", os.path.join(_HERE, "989_m2_double_sided_psi_probe.py"))
_p989 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_p989)
one_case = _p989.one_case


def grid(N, dom, los, his):
    rows = []
    for lo in los:
        for hi in his:
            if lo >= hi:
                continue
            r = one_case(N, dom, lo, hi, verbose=False)
            rows.append((lo, hi, r["psi"], r["A"]))
    return rows


def sign(s, eps=3e-3):
    return "+" if s > eps else ("-" if s < -eps else "0")


def width_invariance(N, dom):
    print("# width-invariance: psi depends only on window width w = hi - lo")
    print("   (log-coordinate translation invariance of the ortho-residual family)")
    for w in [2.4, 2.8, 3.2, 3.8]:
        line = []
        for lo in [-2.4, -2.0, -1.6, -1.2, -0.8]:
            r = one_case(N, dom, lo, round(lo + w, 1), verbose=False)
            line.append("lo%+.1f:%+.5f" % (lo, r["psi"]))
        print("w=%.1f  %s" % (w, "  ".join(line)))


def bisect_width(N, dom, lo, a, b, tol=1e-4):
    """Bisect the zero of psi as a function of window width w at fixed lo."""
    def fw(w):
        return one_case(N, dom, lo, round(lo + w, 3), verbose=False)["psi"]
    fa, fb = fw(a), fw(b)
    assert fa * fb <= 0, "no sign change in [a,b]"
    for _ in range(40):
        m = (a + b) / 2
        fm = fw(m)
        if fa * fm <= 0:
            b, fb = m, fm
        else:
            a, fa = m, fm
        if b - a < tol:
            break
    return (a + b) / 2


def main():
    N = 20001
    dom = 4.0
    print("# psi sign grid: rows=lo, cols=hi   sign: + if psi>3e-3, - if psi<-3e-3, 0 else")
    los = [-2.6, -2.2, -1.8, -1.4, -1.0, -0.6]
    his = [1.0, 1.4, 1.8, 2.2, 2.6, 3.0, 3.4]
    rows = grid(N, dom, los, his)
    d = {(round(lo, 1), round(hi, 1)): psi for (lo, hi, psi, _) in rows}
    print("%-6s" % "lo\\hi" + "".join("%9.1f" % h for h in his))
    for lo in los:
        cells = []
        for hi in his:
            if lo >= hi:
                cells.append("     .    ")
            else:
                psi = d[(round(lo, 1), round(hi, 1))]
                cells.append("%s %+.4f" % (sign(psi), psi))
        print("%-6s" % ("%+.1f" % lo) + "".join("%9s" % c for c in cells))
    print()
    print("# finer hi sweep at fixed lo (1.4..3.0 step .2), psi per window")
    for lo in [-1.2, -1.5, -2.0]:
        line = []
        for hi in np.arange(1.4, 3.01, 0.2):
            r = one_case(N, dom, lo, round(float(hi), 1), verbose=False)
            line.append("%.1f:%+.4f" % (hi, r["psi"]))
        print("lo=%+.1f  %s" % (lo, " | ".join(line)))
    print()
    width_invariance(N, dom)
    print()
    wstar = bisect_width(N, dom, -2.0, 2.80, 2.90)
    print("# w* (zero crossing at lo=-2.0) ~ %.6f  => psi<0 for width > %.4f"
          % (wstar, wstar))


if __name__ == "__main__":
    main()
