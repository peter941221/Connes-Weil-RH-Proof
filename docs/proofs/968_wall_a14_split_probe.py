# Wall-A 1.4 residual: three-piece split of the arch integral (numeric evidence)
#   arch = C*A + I,  need |I| < C*A,  C = log(4pi)+gamma = 3.108, A = ||f||^2.
#   Numerics: NOT a proof; scope = fix the per-piece magnitudes so a Lean
#   pointwise-integrand bound only needs these tolerances.
#   Witness = unitFourierCoreBump = smoothTransition(2-2|x|).
import numpy as np
def smoothTransition(t):
    t=np.asarray(t,float); out=np.zeros_like(t); out[t>=1]=1.0
    core=(t>0)&(t<1); tc=t[core]
    gx=np.exp(-1.0/tc); g1x=np.exp(-1.0/(1.0-tc)); out[core]=gx/(gx+g1x)
    return out
def bump(x):
    a=np.abs(np.asarray(x,float)); return smoothTransition(2-2*a)
def convfft(f):
    n=f.shape[0]; nf=int(2**np.ceil(np.log2(2*n)))
    F=np.fft.rfft(f,nf); return np.fft.irfft(F*F,nf)[:(2*n-1)]
N=40000; dom=4.0
xs=np.linspace(-dom,dom,N); dx=xs[1]-xs[0]
f=bump(xs); full=convfft(f)*dx; center=N-1
A=float(full[center]); C=np.log(4*np.pi)+np.euler_gamma; R=2.0
ys=np.linspace(0,R,4000000)
ks=(np.round(ys/dx)).astype(int)+center
rv=np.where((ks>=0)&(ks<len(full)), full[np.clip(ks,0,len(full)-1)],0.0)
integ=(np.exp(ys/2)*2*rv-2*A)/(np.exp(ys)-np.exp(-ys)); integ[0]=A/2
Itail=2*A*np.log(np.tanh(R/2))
cr=rv-A*np.exp(-ys/2); cross=np.where(cr<0)[0]
y0=ys[cross[0]] if len(cross) else 0.0
Ipos=np.trapezoid(integ[ys<=y0], ys[ys<=y0])
Ineg=np.trapezoid(integ[ys>y0], ys[ys>y0])
Ic=Ipos+Ineg; I=Ic+Itail
print(f"A={A:.6f}  C={C:.6f}  C*A={C*A:.6f}")
print(f"y0 (crossover r(y)=A e^-y/2) ~ {y0:.4f}")
print(f"I(0..y0) +ve = {Ipos:.5f}  |/A = {abs(Ipos)/A:.4f}")
print(f"I(y0..R) -ve = {Ineg:.5f}  |/A = {abs(Ineg)/A:.4f}")
print(f"I(0..R)      = {Ic:.5f}")
print(f"tail y>R     = {Itail:.5f}  |/A = {abs(Itail)/A:.4f}")
print(f"I total      = {I:.6f}  |I|/A = {abs(I)/A:.4f}   (need < C = {C:.4f})")
print(f"headroom C*A - |I| = {C*A-abs(I):.6f}")
