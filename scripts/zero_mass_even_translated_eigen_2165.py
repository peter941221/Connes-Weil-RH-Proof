import numpy as np
from scipy.signal import fftconvolve
from scipy.integrate import simpson
from math import log,pi

def bump(u):
 u=np.asarray(u); a=np.abs(u); out=np.zeros_like(a,float); core=a<=.9; out[core]=1
 tr=(a>.9)&(a<1); t=(a[tr]**2-.9**2)/(1-.9**2)
 q=np.exp(-1/t)/(np.exp(-1/t)+np.exp(-1/(1-t))); out[tr]=1-q
 return out

def Qmat(bs,x,dx,y):
 C=log(4*pi)+0.5772156649015329; n=len(bs); Q=np.zeros((n,n)); m=np.array([simpson(b,x=x) for b in bs])
 mask=y>2*dx; yp=y[mask]
 for i,bi in enumerate(bs):
  for j,bj in enumerate(bs[:i+1]):
   F=fftconvolve(bi,bj,mode='full')*dx; F0=simpson(bi*bj,x=x)
   val=C*F0+simpson((2*np.exp(yp/2)*F[mask]-2*F0)/(np.exp(yp)-np.exp(-yp)),x=yp)
   Q[i,j]=Q[j,i]=val
 return Q,m

for dx in [4e-4,2e-4]:
 L=.7; x=np.arange(-L,L+dx/2,dx); y=np.arange(-2*L,2*L+dx/2,dx)
 specs=[]
 for w in [.04,.06,.08,.10,.12]:
  for c in [0,.06,.10,.14,.18,.22]:
   if c+w <= .346: specs.append((w,c))
 bs=[]
 for w,c in specs:
  b=bump(x/w) if c==0 else bump((x-c)/w)+bump((x+c)/w)
  bs.append(b)
 Q,m=Qmat(bs,x,dx,y); U,s,Vt=np.linalg.svd(m.reshape(1,-1)); N=Vt[1:].T; ev=np.linalg.eigvalsh(N.T@Q@N)
 print('dx',dx,'num',len(specs),'maxeig',ev[-1],'spec',specs[np.argmax(np.abs(N@np.linalg.eigh(N.T@Q@N)[1][:,-1]))])
 print('top',[(specs[i],round(v,4)) for i,v in enumerate(N@np.linalg.eigh(N.T@Q@N)[1][:,-1]) if abs(v)>0.1], 'mass', m@(N@np.linalg.eigh(N.T@Q@N)[1][:,-1]))
