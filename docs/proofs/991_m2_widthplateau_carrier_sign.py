# M.2 evaluates smooth finite-vanishing residuals on windows whose widths match
# the plain Lean carriers narrowC and wideC. The residuals are different tests.
# Numeric only; RH NOT claimed.
import importlib.util, os

_HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("p989", os.path.join(_HERE, "989_m2_double_sided_psi_probe.py"))
p989 = importlib.util.module_from_spec(spec); spec.loader.exec_module(p989)
one = p989.one_case

def carrier(N, dom, lohi, label):
    (lo, hi) = lohi
    r = one(N, dom, lo, hi, verbose=False)
    print("%-24s [%+.1f,%+.1f] M0=%+.1e Mh=%+.1e M1=%+.1e A=%+.5f arch=%+.5f pole=%+.5f primes=%+.5f psi=%+.6f"
          % (label, lo, hi, r["M0"], r["Mh"], r["M1"],
             r["A"], r["arch"], r["pole"], r["prime_sum"], r["psi"]))
    return r

def main():
    print("# Smooth residuals at widths matching, but not equal to, Lean carriers")
    for N in (10001, 20001, 40001):
        carrier(N, 4.0, (-1.2, 1.2), "residual width 2.4")
        carrier(N, 4.0, (-1.5, 1.5), "residual width 3.0")
        print()
    print("# No value transfers to narrowC/wideC without a same-object theorem.")
    print("# RH NOT claimed.")

if __name__ == "__main__":
    main()
