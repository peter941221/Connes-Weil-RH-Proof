# Probe 988: finite-vanishing test g via orthogonal complement of span{1,e^{t/2},e^t}
# g = q - Proj_span(q),  q=smooth bump on (lo,hi)  => M(g,0)=M(g,1/2)=M(g,1)=0
from numpy import pi, euler_gamma
import numpy as np

def smoothTransition(t):
    t=np.asarray(t,float); out=np.zeros_like(t); out[t>=1]=1.0
    core=(t>0)&(t<1); tc=t[core]
    gx=np.exp(-1.0/tc); g1x=np.exp(-1.0/(1.0-tc)); out[core]=gx/(gx+g1x)
    return out

def hbump(x,lo,hi):
    t=np.asarray(x,float); w=(hi-lo)/2.0
    return smoothTransition((t-lo)/w)*smoothTransition((hi-t)/w)

def convfft(f):
    n=f.shape[0]; nf=int(2**np.ceil(np.log2(2*n)))
    F=np.fft.rfft(f,nf); return np.fft.irfft(F*F,nf)[:(2*n-1)]

def arch(g,dx):
    center=(len(g)-1)//2; A=float(g[center]); C=np.log(4*pi)+euler_gamma
    R=2.0; ys=np.linspace(0,R,20000); ks=np.round(ys/dx).astype(int)+center
    rv=np.where((ks>=0)&(ks<len(g)), g[np.clip(ks,0,len(g)-1)],0.0)
    den=np.exp(ys)-np.exp(-ys); integ=np.zeros_like(ys); nz=den!=0
    integ[nz]=(np.exp(ys[nz]/2)*2*rv[nz]-2*A)/(den[nz]); integ[0]=A/2
    I0=np.trapz(integ,ys); It=2*A*np.log(np.tanh(R/2))
    return A, C*A+I0+It

def mel(G,t,c): return np.trapz(np.exp(c*t)*G,t)

def run(N=40001,dom=6.0,lo=0.4,hi=2.2):
    xs=np.linspace(-dom,dom,N); dx=xs[1]-xs[0]
    q=hbump(xs,lo,hi)
    win=q>1e-12
    B=np.column_stack([q*1.0, q*np.exp(xs/2), q*np.exp(xs)])  # windowed exp basis
    # residual orthogonal complement relative to pure-exponentials: use plain exponentials on win
    E=np.column_stack([np.ones(N), np.exp(xs/2), np.exp(xs)])
    # restrict to window rows (avoid ill-conditioning of huge exp)
    m=E[win]
    qv=q[win]
    coef,_,_,_=np.linalg.lstsq(m, qv, rcond=None)
    g=np.zeros_like(q)
    g[win]=qv - E[win]@coef
    # verify vanishing
    M0=mel(g,xs,0.0); Mhalf=mel(g,xs,0.5); M1=mel(g,xs,1.0)
    gc=convfft(g)*dx
    gc_x=(np.arange(len(gc))-(len(g)-1))*dx
    A2,_=arch(gc,dx); _,archv=arch(gc,dx)
    pole=2*float(np.array(mel(gc,gc_x,1j/2)).real)
    def gv(x):
        i=int(round((x-gc_x[0])/dx)); return gc[i] if 0<=i<len(gc) else 0.0
    term2=np.log(2.0)/np.sqrt(2.0)*(gv(2.0)+gv(0.5))
    psi=pole-archv-term2
    print("== finite-vanishing g (orth complement) ==")
    print("vanishing M(g,0)=%.3e  M(g,1/2)=%.3e  M(g,1)=%.3e"%(M0,Mhalf,M1))
    print("max|g|=%.4f  |g|^2 L2 = %.4f"%(np.max(np.abs(g)), np.trapz(g*g, xs)))
    print("conv-square: center A=g2(0)=%.5f"%(A2))
    print("arch=%.5f  pole=%.5f  term2=%.5f (g2(2)=%.2e g2(1/2)=%.2e)"%(archv,pole,term2,gv(2.0),gv(0.5)))
    print("psi(conv^2 g)=pole-arch-term2 = %.6f"%psi)
    print("RH NOT claimed.")

run()
