"""862 - Gamma-phase probe for the route-1 sign slot.

Question (doc 859 / 858c): for the band test f(t)=t^a e^(-t) (a>0), the sign
slot reduces to Re[(Gamma(a+i/2))^4] >= 0.  859 conjectured an asymptotic
"exists a0, forall a>=a0, Re[Gamma(a+i/2)^4] > 0".  This probe tests that
conjecture AND maps the exact positive windows of Re[Gamma(a+i/2)^4].
"""
import math
import mpmath as mp

mp.mp.dps = 60          # high precision near the tiny-argument crossings

def argdeg(a):
    return float(mp.arg(mp.gamma(mp.mpc(a, 0.5)))) * 180.0 / math.pi

def gamma4_sign(a):
    z = mp.gamma(mp.mpc(a, 0.5)) ** 4
    re_ = z.real
    return 1 if re_ > 0 else (-1 if re_ < 0 else 0)

def main():
    print("Part A: sign windows of Re[Gamma(a+i/2)^4] on a in [0.001,4)")
    runs = []
    a = mp.mpf("0.001")
    while a < 4:
        s = gamma4_sign(a)
        if not runs or runs[-1][2] != s:
            runs.append([a, a, s])
        else:
            runs[-1][1] = a
        a += mp.mpf("0.005")
    for lo, hi, s in runs:
        label = "POSITIVE" if s > 0 else ("negative" if s < 0 else "~zero")
        print(f"  a in [{float(lo):.4f},{float(hi):.4f}] -> Re[..^4] {label}")

    print()
    print("Part B: arg(Gamma(a+i/2)) [deg] vs (1/2)ln(a) [deg], 4*arg%360, sign")
    print(f"  {'a':>6} {'arg':>10} {'(1/2)ln a':>10} {'4arg%360':>9} {'sign':>5}")
    for a in [1,2,3,5,10,20,50,100,200,500,1000,2000,5000]:
        ad = argdeg(a)
        pred = (math.log(a)/2.0)*(180.0/math.pi)
        quad = (4*ad) % 360
        print(f"  {a:6d} {ad:+10.3f} {pred:+10.3f} {quad:+9.2f} {gamma4_sign(a):+5d}")

    print()
    print("VERDICT")
    print("  1) two POSITIVE windows:", [ (float(lo),float(hi)) for lo,hi,s in runs if s>0 ])
    print("  2) arg ~ (1/2)ln a => 4arg wraps 2pi infinitely often => no eventual a0")

main()