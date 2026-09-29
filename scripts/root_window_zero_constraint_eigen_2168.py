import numpy as np
from scipy.signal import fftconvolve
from scipy.integrate import simpson
from math import log,pi

def bump(u):
 u=np.asarray(u); a=np.abs(u); out=np.zeros_like(a,float); core=a<=.9; out[core]=1
 tr=(a>.9)&(a<1); t=(a[tr]**2-.9**2)/(1-.9**2); q=np.exp(-1/t)/(np.exp(-1/t)+np.exp(-1/(1-t))); out[tr]=1-q; return out

def eval_basis(specs,dx=.001,L=.7):
 x=np.arange(-L,L+dx/2,dx); y=np.arange(-2*L,2*L+dx/2,dx); bs=[]
 for w,c in specs: bs.append(bump((x-c)/w))
 n=len(bs); C=log(4*pi)+0.5772156649015329; Q=np.zeros((n,n));
 mask=y>2*dx; yp=y[mask]; den=np.exp(yp)-np.exp(-yp); ew=2*np.exp(yp/2)
 for i in range(n):
  for j in range(i,n):
   F=fftconvolve(bs[i][::-1],bs[j],mode='full')*dx # involution bi(-t), but bump is symmetric around c => reverse handles
   F0=simpson(bs[i][::-1]*bs[j],x=x)
   val=C*F0+simpson((ew*F[mask]-2*F0)/den,x=yp)
   Q[i,j]=val; Q[j,i]=val
 # Laplace constraints at s real 0,.5,1; integrate exp(s x) bi(x)
 A=np.array([[simpson(np.exp(s*x)*b,x=x) for b in bs] for s in [0,.5,1]])
 return x,bs,Q,A

Lroot=log(2)/2
# shifted bumps all strictly inside +-root window; include asymmetrical centers
specs=[]
for w in [.025,.04,.06,.08]:
 for c in [-.25,-.18,-.1,0,.1,.18,.25]:
  if abs(c)+w < Lroot-.005: specs.append((w,c))
# add symmetric and antisymmetric pairs as separate linear combinations? Individual basis spans them.
x,bs,Q,A=eval_basis(specs)
# nullspace A
U,s,Vt=np.linalg.svd(A); N=Vt[3:].T
R=N.T@Q@N; ev=np.linalg.eigvalsh((R+R.T)/2)
print('Lroot',Lroot,'basis',len(specs),'constraint sv',s,'eig min/max',ev[0],ev[-1])
# Also impose detection at rho = .6+14i via complex constraint, then nullspace
rho=.6+14.134725j
Ac=np.array([[simpson(np.exp((sig+1j*14.134725)*x)*b,x=x) for b in bs] for sig in [.6]])
# real constraints: Re/Im detection? For nullspace add three real rows + Re/Im at rho, but this is homogeneous detection=0; check positive on nullspace
A5=np.vstack([A, Ac.real, Ac.imag]); U,s,Vt=np.linalg.svd(A5); N2=Vt[5:].T; R2=N2.T@Q@N2; ev2=np.linalg.eigvalsh((R2+R2.T)/2)
print('with detector-zero constraints sv',s,'eig min/max',ev2[0],ev2[-1])
# generalized candidate satisfying vanish constraints but normalized detection 1: min norm solve and Q
# optimize Q over affine A5 a = target [0..,1,0] in real coeffs, use least-norm then top eig null
btarget=np.r_[np.zeros(3),1.,0.]
a0=A5.T@np.linalg.solve(A5@A5.T,btarget)
print('a0 residual',np.max(np.abs(A5@a0-btarget)),'Q0',a0@Q@a0,'norm',np.linalg.norm(a0))
if N2.shape[1]:
 vals=[]
 for t in np.linspace(-3,3,31):
  # random direction max? sample along top eig
  pass
 v=N2@np.linalg.eigh(R2)[1][:,-1]
 for t in [-100,-30,-10,-3,-1,0,1,3,10,30,100]: vals.append((t,(a0+t*v)@Q@(a0+t*v)))
 print('affine along top null',vals)
