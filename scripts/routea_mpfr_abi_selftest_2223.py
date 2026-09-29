"""Independent ABI smoke for the MPFR backend used by record 2223."""
import importlib.util
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sp = importlib.util.spec_from_file_location(
    "mpfr2223", ROOT / "scripts" / "routea_weighted_zero_mpfr_exp_binding_2223.py")
m = importlib.util.module_from_spec(sp)
sp.loader.exec_module(m)

src, lo, hi = m.M(), m.M(), m.M()
try:
    src.set_d(1.0)
    for fn, truth, label in ((m._lib.mpfr_exp, math.e, "exp(1)"),
                             (m._lib.mpfr_sin, math.sin(1.0), "sin(1)"),
                             (m._lib.mpfr_cos, math.cos(1.0), "cos(1)")):
        fn(m.C.byref(lo.x), m.C.byref(src.x), m.RNDD)
        fn(m.C.byref(hi.x), m.C.byref(src.x), m.RNDU)
        lv, hv = lo.get_d(m.RNDD), hi.get_d(m.RNDU)
        assert lv <= truth <= hv, (label, lv, truth, hv)
        print(label, repr(lv), repr(hv), "contains=True", flush=True)
finally:
    src.clear()
    lo.clear()
    hi.clear()
