# M.2 probe — finite-vanishing test g with TWO-SIDED support so that
#   A=(g*g)(0) = ||g||^2 is non-trivial, M(g,0)=M(g,1/2)=M(g,1)=0 exactly
#   (single lstsq), and psi = pole - arch - term2 is measured non-degenerately.
#
# Design: exactly 988's construction, but q is a TWO-SIDED smooth bump
#   (lo < 0 < hi) so the residual g has support on both signs.  This is the
#   "correctly-dangled" test 988 explicitly said was missing.
#
# RH NOT claimed.  Numeric evidence only.
import numpy as np
from numpy import pi, euler_gamma

def smoothTransition(t):
    t = np.asarray(t, float); out = np.zeros_like(t); out[t >= 1] = 1.0
    core = (t > 0) & (t < 1); tc = t[core]
    gx = np.exp(-1.0/tc); g1x = np.exp(-1.0/(1.0-tc)); out[core] = gx/(gx+g1x)
    return out

def hbump(x, lo, hi):
    t = np.asarray(x, float); w = (hi-lo)/2.0
    return smoothTransition((t-lo)/w) * smoothTransition((hi-t)/w)

def convSquare(f):
    """Correct healthy conv-square: (g* ⋆ g)(x) with g*(t)=conj(g(-t)).
    For real g this is irfft(|rfft(g)|^2)  =>  at 0 it is ALWAYS ||g||^2 >= 0.
    The old 987/988 convfft used rfft(g)^2 (plain self-conv), which corrupts
    the center value for non-even g (could go negative — a Lean-invalid sign)."""
    n = f.shape[0]; nf = int(2**np.ceil(np.log2(2*n)))
    F = np.fft.rfft(f, nf)
    return np.fft.irfft(F*np.conj(F), nf)[:(2*n-1)]

def mel(G, t, c): return np.trapz(np.exp(c*t)*G, t)

def one_case(N, dom, lo, hi, verbose=True):
    xs = np.linspace(-dom, dom, N); dx = xs[1]-xs[0]
    q = hbump(xs, lo, hi)
    win = q > 1e-12
    E = np.column_stack([np.ones(N), np.exp(xs/2), np.exp(xs)])
    m = E[win]; qv = q[win]
    coef, _, _, _ = np.linalg.lstsq(m, qv, rcond=None)
    g = np.zeros_like(q); g[win] = qv - m@coef
    M0  = mel(g, xs, 0.0)
    Mh  = mel(g, xs, 0.5)
    M1  = mel(g, xs, 1.0)
    # Correct healthy conv-square: irfft(|F|^2) has lag-0 / x=0 at INDEX 0.
    n = len(g); nf = int(2**np.ceil(np.log2(2*n)))
    G = np.fft.rfft(g, nf)
    gc = np.fft.irfft(G*np.conj(G), nf) * dx   # (g* star g)(k.dx), x=0 at k=0
    A = float(gc[0])
    lp = float(np.trapz(g*g, xs))   # ||g||2 ; Lean: (g* star g)(0) = ||g||2
    assert abs(A - lp) < 5e-3, f"conv-square center mismatch: A={A:.6f} vs ||g||^2={lp:.6f}"
    def g_at(x):
        k = int(round(x/dx))
        return gc[k] if 0 <= k < nf else 0.0
    # arch reads along +y from x=0 (gc[0]=A); CCM25 healthy arch form.
    R = 2.0; ys = np.linspace(0, R, 20000); ks = np.round(ys/dx).astype(int)
    rw = np.where((ks>=0)&(ks<nf), gc[np.clip(ks,0,nf-1)], 0.0)
    den = np.exp(ys)-np.exp(-ys); integ = np.zeros_like(ys); nz = den!=0
    integ[nz] = (np.exp(ys[nz]/2)*2*rw[nz]-2*A)/(den[nz]); integ[0] = A/2
    I0 = np.trapz(integ, ys); It = 2*A*np.log(np.tanh(R/2))
    C = np.log(4*pi)+euler_gamma
    archv = C*A + I0 + It
    pole = 2*float(np.array(mel(gc, (np.arange(nf))*dx, 1j/2)).real)
    term2 = np.log(2.0)/np.sqrt(2.0)*(g_at(2.0)+g_at(0.5))
    psi = pole - archv - term2
    if verbose:
        print("== two-sided finite-vanishing g  window=[%.2f, %.2f] =="%(lo,hi))
        print("vanishing M(g,0)=%.3e  M(g,1/2)=%.3e  M(g,1)=%.3e"%(M0,Mh,M1))
        print("max|g|=%.4f  L2=%.4f  A=g2(0)=%.5f (assert |A-L2| ok)"%(np.max(np.abs(g)), lp, A))
        print("arch=%.5f  pole=%.5f  term2=%.5f  (g(2)=%.2e g(1/2)=%.2e)"%(archv,pole,term2,g_at(2.0),g_at(0.5)))
        print("psi=pole-arch-term2 = %.6f"%psi)
        print("RH NOT claimed.")
    return dict(M0=M0, Mh=Mh, M1=M1, maxg=np.max(np.abs(g)),
                L2=lp, A=A, arch=archv, pole=pole, term2=term2,
                psi=psi, gv2=g_at(2.0), gv_half=g_at(0.5))
if __name__ == "__main__":
    print("### symmetric full-width windows")
    for lohi in [(-1.0,1.0),(-1.5,1.5),(-2.0,2.0),(-1.0,2.0)]:
        one_case(40001, 4.0, lohi[0], lohi[1])
        print()
    print("### window scan (compact rows; only M0 shown for vanishing-check)")
    for lohi in [(-0.8,2.0),(-1.0,2.0),(-1.2,2.0),(-1.5,2.0),(-2.0,2.5),(-1.0,3.0),(-0.5,1.5),(-0.7,2.2),(-1.5,3.0)]:
        r = one_case(40001, 4.0, lohi[0], lohi[1], verbose=False)
        print("[%+.1f,%+.1f] M0=%.1e Mh=%.1e M1=%.1e A=%+.5f arch=%+.5f pole=%+.5f term2=%+.5f psi=%+.6f g2=%.2e gHalf=%.2e"%(
            lohi[0],lohi[1], r['M0'],r['Mh'],r['M1'], r['A'],r['arch'],r['pole'],r['term2'], r['psi'], r['gv2'], r['gv_half']))