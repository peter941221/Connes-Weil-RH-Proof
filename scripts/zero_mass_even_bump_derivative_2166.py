import numpy as np
from scipy.signal import fftconvolve
from scipy.integrate import simpson
from math import log,pi

def bump(u):
 u=np.asarray(u); a=np.abs(u); out=np.zeros_like(a,float); core=a<=.9; out[core]=1
 tr=(a>.9)&(a<1); t=(a[tr]**2-.9**2)/(1-.9**2)
 q=np.exp(-1/t)/(np.exp(-1/t)+np.exp(-1/(1-t))); out[tr]=1-q
 return out

def arch_from(f,dx,x,y):
 C=log(4*pi)+0.5772156649015329; F=fftconvolve(f,f,mode='full')*dx; F0=simpson(f*f,x=x); mask=y>2*dx; yp=y[mask]; Fy=F[mask]
 return C*F0+simpson((2*np.exp(yp/2)*Fy-2*F0)/(np.exp(yp)-np.exp(-yp)),x=yp),F0,simpson(f,x=x)
for w in [.15,.2,.25,.3,.346]:
 for ord in [1,2,3,4]:
  dx=2e-4; L=.7; x=np.arange(-L,L+dx/2,dx); y=np.arange(-2*L,2*L+dx/2,dx); b=bump(x/w)
  # central finite derivative iterated
  f=b.copy()
  for _ in range(ord): f=np.gradient(f,dx,edge_order=2)
  # enforce parity: odd order odd, even even, then support enough
  a,F0,m=arch_from(f,dx,x,y)
  print('w',w,'ord',ord,'arch',a,'mass',m,'F0',F0)
