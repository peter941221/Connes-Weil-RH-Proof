import numpy as np
from scipy.signal import fftconvolve
from scipy.integrate import simpson
from math import log,pi

def bump(u):
 u=np.asarray(u); a=np.abs(u); out=np.zeros_like(a,float); core=a<=.9; out[core]=1
 tr=(a>.9)&(a<1); t=(a[tr]**2-.9**2)/(1-.9**2); q=np.exp(-1/t)/(np.exp(-1/t)+np.exp(-1/(1-t))); out[tr]=1-q; return out

def arch(f,dx,x,y):
 F=fftconvolve(f,f,mode='full')*dx; F0=simpson(f*f,x=x); mask=y>2*dx; yp=y[mask]
 C=log(4*pi)+0.5772156649015329
 return C*F0+simpson((2*np.exp(yp/2)*F[mask]-2*F0)/(np.exp(yp)-np.exp(-yp)),x=yp),F0,simpson(f,x=x)
for dx in [4e-4,2e-4]:
 L=.7; x=np.arange(-L,L+dx/2,dx); y=np.arange(-2*L,2*L+dx/2,dx)
 print('dx',dx)
 for w in [.1,.15,.2,.25,.3,.333,.346,.4]:
  f=bump(x/w)
  # D_a = d/dx + a
  for a in [1,.5,0]: f=np.gradient(f,dx,edge_order=2)+a*f
  A,F0,m=arch(f,dx,x,y)
  print(w,A,m,F0)
