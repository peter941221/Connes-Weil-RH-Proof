# M.2 narrowed to the Lean carriers narrowC (support [-1.2,1.2], width 2.4)
# and wideC (support [-1.5,1.5], width 3.0).  Reuses 989 one_case (single source).
# Numeric only; RH NOT claimed.
import importlib.util, os
import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("p989", os.path.join(_HERE, "989_m2_double_sided_psi_probe.py"))
p989 = importlib.util.module_from_spec(spec); spec.loader.exec_module(p989)
one = p989.one_case

def carrier(N, dom, lohi, label):
    (lo, hi) = lohi
    r = one(N, dom, lo, hi, verbose=False)
    print("%-24s [%+.1f,%+.1f] M0=%+.1e Mh=%+.1e M1=%+.1e A=%+.5f arch=%+.5f pole=%+.5f term2=%+.5f psi=%+.6f"
          % (label, lo, hi, r["M0"], r["Mh"], r["M1"],
             r["A"], r["arch"], r["pole"], r["term2"], r["psi"]))
    return r

def main():
    print("# M2WidthPlateau carrier sign - narrowC vs wideC (resolution scan)")
    for N in (10001, 20001, 40001):
        carrier(N, 4.0, (-1.2, 1.2), "narrowC [-1.2,1.2]")
        carrier(N, 4.0, (-1.5, 1.5), "wideC   [-1.5,1.5]")
        print()
    print("# RH NOT claimed; values are numerics, not Lean-theorem signs.")

if __name__ == "__main__":
    main()
