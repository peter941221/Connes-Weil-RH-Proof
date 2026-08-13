# M.2 scan (990): evaluate the complete Weil functional on the smooth
# finite-vanishing test family from probe 989.
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
    return "POS" if s > eps else ("NEG" if s < -eps else "NEAR0")


def width_invariance(N, dom):
    print("# translation check at fixed support width")
    for w in [2.4, 2.8, 3.2, 3.8]:
        line = []
        for lo in [-2.4, -2.0, -1.6, -1.2, -0.8]:
            r = one_case(N, dom, lo, round(lo + w, 1), verbose=False)
            line.append("lo%+.1f:%+.5f" % (lo, r["psi"]))
        print("w=%.1f  %s" % (w, "  ".join(line)))


def minimum_convergence(dom, lo, width):
    print("# resolution check near the sampled minimum (width=%.1f)" % width)
    for sample_count in (10001, 20001, 40001, 80001, 160001):
        result = one_case(
            sample_count,
            dom,
            lo,
            lo + width,
            verbose=False,
        )
        print(
            "N=%6d psi=%+.12e arch=%+.12e primes=%+.12e max|M|=%.3e"
            % (
                sample_count,
                result["psi"],
                result["arch"],
                result["prime_sum"],
                result["moment_error"],
            )
        )


def main():
    N = 20001
    dom = 5.0
    print("# complete-QW grid: POS/NEG outside +/-3e-3, NEAR0 otherwise")
    los = [-2.6, -2.2, -1.8, -1.4, -1.0, -0.6]
    his = [1.0, 1.4, 1.8, 2.2, 2.6, 3.0, 3.4]
    rows = grid(N, dom, los, his)
    d = {(round(lo, 1), round(hi, 1)): psi for (lo, hi, psi, _) in rows}
    print("%-6s" % "lo\\hi" + "".join("%9.1f" % h for h in his))
    for lo in los:
        cells = []
        for hi in his:
            if lo >= hi:
                cells.append(".")
            else:
                psi = d[(round(lo, 1), round(hi, 1))]
                cells.append("%s:%+.4f" % (sign(psi), psi))
        print("%-6s" % ("%+.1f" % lo) + "".join("%14s" % c for c in cells))
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
    samples = [
        (width, one_case(N, dom, -2.0, -2.0 + width, verbose=False)["psi"])
        for width in np.arange(1.6, 5.01, 0.2)
    ]
    print("# width sweep at lo=-2.0")
    print("  ".join("%.1f:%+.5f" % item for item in samples))
    minimum = min(samples, key=lambda item: item[1])
    print(
        "# scan verdict: no negative value; minimum psi=%+.8f at width=%.1f"
        % (minimum[1], minimum[0])
    )
    print()
    minimum_convergence(dom, -2.0, minimum[0])


if __name__ == "__main__":
    main()
