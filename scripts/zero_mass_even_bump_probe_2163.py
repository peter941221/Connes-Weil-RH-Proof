import numpy as np
from scipy.signal import fftconvolve
from scipy.integrate import simpson
from math import exp, log, pi

def bump(u):
    u=np.asarray(u)
    a=np.abs(u)
    out=np.zeros_like(a,dtype=float)
    core=a<=.9
    out[core]=1.0
    tr=(a>.9)&(a<1)
    t=(a[tr]**2-.9**2)/(1-.9**2)
    # smoothTransition t = exp(-1/t)/(exp(-1/t)+exp(-1/(1-t)))
    q=np.exp(-1/t)/(np.exp(-1/t)+np.exp(-1/(1-t)))
    out[tr]=1-q
    return out

def arch(w1,w2,dx=1e-4,L=0.8):
    x=np.arange(-L,L+dx/2,dx)
    f=bump(x/w1)-(w1/w2)*bump(x/w2)
    # centered convolution, y from -2L to 2L
    F=fftconvolve(f,f,mode='full')*dx
    y=np.arange(-2*L,2*L+dx/2,dx)
    # align lengths
    assert len(y)==len(F), (len(y),len(F))
    F0=simpson(f*f,x=x)
    yp=y[y>2*dx]
    Fi=F[y>2*dx]
    num=2*np.exp(yp/2)*Fi-2*F0
    den=np.exp(yp)-np.exp(-yp)
    I=simpson(num/den,x=yp)
    C=log(4*pi)+0.5772156649015329
    return C*F0+I, F0, simpson(f,x=x), np.max(np.abs(f))

for dx in [4e-4,2e-4,1e-4]:
  print('dx',dx)
  for w2 in [0.20,0.25,0.30,0.346]:
    vals=[]
    for rat in [0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9]:
      w1=rat*w2
      a,F0,m,mx=arch(w1,w2,dx=dx,L=.7)
      vals.append((a,rat,F0))
    best=max(vals)
    print('w2',w2,'best',best,'all',[(round(a,5),r) for a,r,_ in vals])
