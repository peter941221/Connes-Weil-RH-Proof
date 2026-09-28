import math
import sys
from pathlib import Path
from mpmath import mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_high_order_tail_price_2063 as h

mp.dps = 40
K = mp.mpf(30)

def integral_bound(a, b):
    if a >= 1:
        return mp.quad(lambda s: mp.e**(-K / s) * s**(-b), [mp.mpf("0"), mp.mpf("1")])
    first = mp.sqrt(2) * mp.quad(lambda s: mp.e**(-K / s) * s**(-b), [mp.mpf("0"), mp.mpf("0.5")])
    second = mp.sqrt(2) * (mp.mpf(2) ** b) * mp.e**(-K)
    return first + second

for n in (12, 24, 36, 48):
    terms = h.derivative_terms(n)
    bound = mp.mpf(0)
    for (a, b, p), c in terms.items():
        bound += abs(c) * K**p * integral_bound(a, b)
    measured = mp.mpf(h.total_variation(n))
    print(n, mp.nstr(bound, 12), mp.nstr(measured, 12), mp.nstr(bound / measured, 8))
