#!/usr/bin/env python3
"""Exploratory: P094 center exact value, candidate bars, denominator growth."""
import os, sys
from fractions import Fraction as F
sys.path.insert(0, "scripts")
import gen_2663_slots as S

s = S.slots(94)
ph = S.read(s["phase_module"] + ".lean")
tb = S.read(s["table_module"] if s["table_module"].endswith(".lean") else s["table_module"] + ".lean")
ph_val = S.pair(ph, "phaseValue2658P094")
integral = S.pair(tb, "complexPanelIntegral2648P094")
c_re = s["amp_val"] * (ph_val[0]*integral[0] - ph_val[1]*integral[1])
c_im = s["amp_val"] * (ph_val[0]*integral[1] + ph_val[1]*integral[0])
print("P094 center re =", float(c_re), " im =", float(c_im))
print("num digits re:", len(str(abs(c_re.numerator))), "den digits:", len(str(c_re.denominator)))
# 15-sig-digit bars around c_re
import math
def bars15(x):
    if x == 0: return F(0), F(0)
    e = math.floor(math.log10(abs(float(x))))
    step = F(10) ** (e - 15)
    lo = (x // step) * step
    hi = -((-x) // step) * step
    return lo, hi
lo, hi = bars15(c_re)
print("bar re lo =", float(lo), " hi =", float(hi), " width =", float(hi-lo))
# half-ulp check: hi - c_re relative
print("rel half-width:", float((hi - c_re)/abs(c_re)))
# denominator growth over all 190 centers
tot = F(0)
maxden = 0
for k in range(190):
    sk = S.slots(k)
    phk = S.pair(S.read(sk["phase_module"] + ".lean"), f"phaseValue2658P{sk['tag']}")
    tk = S.read(sk["table_module"] if sk["table_module"].endswith(".lean") else sk["table_module"] + ".lean")
    ik = S.pair(tk, f"complexPanelIntegral2648P{sk['tag']}")
    ck = sk["amp_val"] * (phk[0]*ik[0] - phk[1]*ik[1])
    tot += ck
    nd = len(str(abs(ck.denominator)))
    maxden = max(maxden, nd)
print("max per-panel den digits:", maxden)
print("sum den digits:", len(str(abs(tot.denominator))), "num digits:", len(str(abs(tot.numerator))))
print("sum re =", float(tot))
