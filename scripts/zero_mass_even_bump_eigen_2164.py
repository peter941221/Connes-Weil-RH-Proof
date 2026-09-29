import numpy as np
from scipy.signal import fftconvolve
from scipy.integrate import simpson
from math import exp, log, pi

def bump(u):
    u=np.asarray(u); a=np.abs(u); out=np.zeros_like(a,dtype=float)
    core=a<=.9; out[core]=1.0
    tr=(a>.9)&(a<1); t=(a[tr]**2-.9**2)/(1-.9**2)
    # stable in transition away from endpoints
    q=np.exp(-1/t)/(np.exp(-1/t)+np.exp(-1/(1-t)))
    out[tr]=1-q
    return out

def Qmat(ws,dx=2e-4,L=.7):
    x=np.arange(-L,L+dx/2,dx); y=np.arange(-2*L,2*L+dx/2,dx)
    bs=[bump(x/w) for w in ws]
    C=log(4*pi)+0.5772156649015329
    Q=np.zeros((len(ws),len(ws)))
    mass=np.array([simpson(b,x=x) for b in bs])
    for i,bi in enumerate(bs):
      for j,bj in enumerate(bs[:i+1]):
        F=fftconvolve(bi,bj,mode='full')*dx
        F0=simpson(bi*bj,x=x)
        mask=y>2*dx
        yp=y[mask]; Fy=F[mask]
        val=C*F0+simpson((2*np.exp(yp/2)*Fy-2*F0)/(np.exp(yp)-np.exp(-yp)),x=yp)
        Q[i,j]=Q[j,i]=val
    return Q,mass

for ws in [[.10,.18,.26,.346],[.08,.14,.20,.26,.32,.346],[.05,.10,.16,.22,.28,.34]]:
 Q,m=Qmat(ws)
 # nullspace of mass row via SVD
 U,s,Vt=np.linalg.svd(m.reshape(1,-1)); N=Vt[1:].T
 R=N.T@Q@N; ev=np.linalg.eigvalsh(R)
 print('ws',ws,'m',m,'eig',ev,'max',ev[-1])
 # best coeff in null space normalized
 v=N@np.linalg.eigh(R)[1][:,-1]
 print('coeff',v,'mass',m@v,'Q',v@Q@v)
