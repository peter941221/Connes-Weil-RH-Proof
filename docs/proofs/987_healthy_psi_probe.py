import numpy as np
from numpy import pi, euler_gamma

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

def arch_terms(g, dx):
    center = (len(g)-1)//2
    A = float(g[center])
    C = np.log(4*pi) + euler_gamma
    R = 2.0
    ys = np.linspace(0, R, 20000)
    ks = np.round(ys/dx).astype(int)+center
    rv = np.where((ks>=0)&(ks<len(g)), g[np.clip(ks,0,len(g)-1)], 0.0)
    den = np.exp(ys)-np.exp(-ys)
    integ = np.zeros_like(ys); nz = den!=0
    integ[nz] = (np.exp(ys[nz]/2)*2*rv[nz]-2*A)/(den[nz])
    integ[0]=A/2
    I0 = np.trapz(integ, ys)
    It = 2*A*np.log(np.tanh(R/2))
    I = I0+It
    return A, I0, It, I, C*A+I

def melliF(g, t, s):
    return np.trapz(np.exp(s*t)*g, t)

def run(N=40001, dom=4.0):
    xs = np.linspace(-dom, dom, N); dx = xs[1]-xs[0]
    f = bump(xs)
    g = convfft(f)*dx
    gx = (np.arange(len(g)) - (N-1))*dx
    A, I0, It, I, arch = arch_terms(g, dx)
    C = np.log(4*pi)+euler_gamma
    Mg = melliF(g, gx, 1j/2)
    pole = 2*float(np.array(Mg).real)
    v2 = np.log(2.0)
    def gval(x):
        i = int(round((x - gx[0])/dx))
        return g[i] if 0 <= i < len(g) else 0.0
    term2 = v2/np.sqrt(2.0)*(gval(2.0)+gval(0.5))
    M0 = melliF(g, gx, 0.0); Mhalf = melliF(g, gx, 0.5); M1 = melliF(g, gx, 1.0)
    psi = pole - arch - term2
    print("== 986 bump conv-square (log coord) ==")
    print("A=(f*f)(0)=%.5f C=%.5f I=%.5f arch=%.5f"%(A,C,I,arch))
    print("pole=2Re M(g,i/2)=%.5f"%pole)
    print("term2=%.5f (g(2)=%.3e g(1/2)=%.3e)"%(term2,gval(2.0),gval(0.5)))
    print("psi=pole-arch-term2=%.5f"%psi)
    print("vanishing @0=%.4f @1/2=%.4f @1=%.4f (0 needed for crit domain)"%(M0,Mhalf,M1))
    print("RH NOT claimed.")
run()
