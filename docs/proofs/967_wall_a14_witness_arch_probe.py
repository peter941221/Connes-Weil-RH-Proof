# Wall-A 1.4 residual: numeric evidence for the EXPLICIT clean witness.
#   witness = unitFourierCoreBump = smoothTransition(2 - 2|x|)
#   arch(f*f) = C*A + I,  C = log(4*pi)+gamma,  A = (f*f)(0) = ||f||^2,
#   I = 2 * Int_{y>0} ( e^{y/2} r(y) - A )/(e^y - e^{-y}) dy,  r = Re(f*f).
import numpy as np

def smoothTransition(t):
    t = np.asarray(t, float); out = np.zeros_like(t); out[t >= 1] = 1.0
    core = (t > 0) & (t < 1); tc = t[core]
    gx = np.exp(-1.0/tc); g1x = np.exp(-1.0/(1.0-tc)); out[core] = gx/(gx+g1x)
    return out

def bump(x):
    a = np.abs(np.asarray(x, float)); return smoothTransition(2 - 2*a)

def convfft(f):
    n = f.shape[0]; nf = int(2**np.ceil(np.log2(2*n)))
    F = np.fft.rfft(f, nf); return np.fft.irfft(F*F, nf)[:(2*n-1)]

def eval_arch(N):
    dom = 4.0; xs = np.linspace(-dom, dom, N); dx = xs[1]-xs[0]
    f = bump(xs); full = convfft(f)*dx
    center = N-1; A = float(full[center])
    C = np.log(4*np.pi) + np.euler_gamma
    R = 2.0
    ys = np.linspace(0, R, 20000)
    ks = np.round(ys/dx).astype(int)+center
    rv = np.where((ks >= 0) & (ks < len(full)), full[np.clip(ks, 0, len(full)-1)], 0.0)
    integ = (np.exp(ys/2)*2*rv - 2*A)/(np.exp(ys)-np.exp(-ys))
    integ = integ.copy(); integ[0] = A/2
    I_0R = np.trapezoid(integ, ys)
    I_tail = 2*A*np.log(np.tanh(R/2))
    I = I_0R + I_tail
    arch = C*A + I
    return A, I_0R, I_tail, I, arch

A, I0, Itail, I, arch = eval_arch(20000)
C = np.log(4*np.pi) + np.euler_gamma
print("== unitFourierCoreBump (smoothTransition(2-2|x|)), rIn=1/2 rOut=1 ==")
print("A  = (f*f)(0) = ||f||^2      =", f"{A:.6f}")
print("C  = log(4*pi)+gamma         =", f"{C:.6f}")
print("I(0..R)                      =", f"{I0:.6f}")
print("I(tail y>2) (exact)          =", f"{Itail:.6f}")
print("I total                      =", f"{I:.6f}")
print("arch = C*A + I               =", f"{arch:.6f}   (>0)")
print("|I|/A                        =", f"{abs(I)/A:.4f}", "  (need < C =", f"{C:.4f}", ")")
print("headroom C*A - |I|           =", f"{C*A - abs(I):.6f}")
