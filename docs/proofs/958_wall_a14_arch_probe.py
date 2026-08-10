# Wall-A 1.4: numeric probe of the Eq.3.7 arch/prime identity
#   target: 2*arch(f*f) + (globalSum - restrictedSum) = 0
# f supported in (1.5,2.5), f(2)=1 smooth bump (matches route commonBump spec).
# Numerics are NOT a proof; scope: proxy on a representative bump (the route
# commonBump is a Classical.choose, not numerically explicit).
import mpmath as mp
from sympy import factorint
import math
mp.mp.dps = 80

A = mp.mpf('1.5'); B = mp.mpf('2.5')
def phi(t):
    if t <= 0 or t >= 1:
        return mp.mpf(0)
    return mp.exp(-1/(t*(1-t)))
PHI_MID = phi(mp.mpf('0.5'))
def f(x):
    return phi((x-A)/(B-A))/PHI_MID

def conv(x):
    lo = max(-B, x-B)
    hi = min(-A, x-A)
    if hi <= lo:
        return mp.mpf(0)
    return mp.quad(lambda t: f(-t)*f(x-t), [lo, hi])

def is_prime_pow(n):
    if n < 2:
        return False
    return len(factorint(n)) == 1

def vonMangoldt(n):
    fac = factorint(n)
    if len(fac) == 1:
        return mp.log(mp.mpf(list(fac)[0]))
    return mp.mpf(0)

def finitePrimeTerm(n):
    z = mp.log(mp.mpf(n))
    return vonMangoldt(n)/mp.sqrt(mp.mpf(n)) * (conv(z) + conv(-z))

cq = mp.quad(lambda t: f(t)**2, [A,B])
cc0 = conv(mp.mpf(0))
assert abs(cq-cc0) < mp.mpf('1e-40'), (cq, cc0)
print("||f||^2 =", mp.nstr(cq,16), "  conv(0) =", mp.nstr(cc0,16))

# visible prime-powers: scan n with |log n| within conv support (~[0,1.7])
terms = {}
for n in range(2, 2000):
    if is_prime_pow(n):
        t = finitePrimeTerm(n)
        if abs(t) > mp.mpf('1e-80'):
            terms[n] = t
print("visible prime-powers (finitePrimeTerm != 0):", sorted(terms) if terms else "NONE")
for n in sorted(terms):
    print(f"  n={n:4d}  log n={mp.nstr(mp.log(mp.mpf(n)),8):>10}  term={mp.nstr(terms[n],20)}")
globalSum = mp.fsum(terms.values())
print("globalSum =", mp.nstr(globalSum, 25))


f0 = conv(mp.mpf(0))
def integrand(y):
    if y <= 0:
        return mp.mpf(0)
    e = mp.exp(y)
    num = mp.exp(y/2)*(conv(y)+conv(-y)) - 2*f0
    return num/(e - 1/e)
# conv nonzero only around y in [0,~1.7]; tail y>2 the numerator = -2f0.
archint = mp.quad(integrand, [mp.mpf('1e-80'), mp.mpf('3')])
tail = mp.quad(lambda y: -2*f0/(mp.exp(y)-mp.exp(-y)), [mp.mpf('3'), 200])
archint_total = archint + tail
arch = (mp.log(4*mp.pi) + mp.euler)*f0 + archint_total
print("archint[0,3]  =", mp.nstr(archint,25))
print("archint tail  =", mp.nstr(tail,25))
print("arch(Eq3.7)   =", mp.nstr(arch,25))
print("2*arch        =", mp.nstr(2*arch,25))

def restrictedSum(lam):
    return mp.fsum(t for n,t in terms.items() if mp.mpf(n) <= lam*lam)
print("\nbalance 2*arch + (globalSum - restrictedSum):")
for lam in [1.5, 2, 3, 5, 10, 100]:
    r = restrictedSum(mp.mpf(lam))
    bal = 2*arch + (globalSum - r)
    print(f"  lambda={lam:6.1f}  restricted={mp.nstr(r,20):>24}  balance={mp.nstr(bal,20)}")