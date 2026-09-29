import numpy as np, math
from scipy.signal import fftconvolve
from scipy.linalg import eigh
C=math.log(4*math.pi)+np.euler_gamma

def arch(f,dx):
 n=f.size;c=n-1;F=fftconvolve(f[::-1],f,mode='full')*dx;f0=F[c]
 y=dx*np.arange(1,c+1,dtype=float);fy=F[c+1:]
 # The constant -2F(0) part continues beyond the compact correlation;
 # retain its exact analytic tail rather than silently dropping a term of
 # order F(0) at these short support radii.
 tail=f0*math.log(math.tanh(y[-1]/2))
 return C*f0+np.trapezoid((np.expm1(y/2)*fy+(fy-f0))/np.sinh(y),y)+tail

def von_mangoldt(n):
 if n<2: return 0.0
 m=n; p=2; found=None
 while p*p<=m:
  if m%p==0:
   found=p
   while m%p==0: m//=p
   if m!=1: return 0.0
   return math.log(p)
  p+=1
 return math.log(n)

def prime_sum(f,dx,r):
 n=f.size; c=n-1; corr=fftconvolve(f[::-1],f,mode='full')*dx
 out=0.0; terms=[]
 for nidx in range(2,int(math.exp(2*r))+1):
  lam=von_mangoldt(nidx)
  if lam==0: continue
  lag=math.log(nidx)
  if lag > (n-1)*dx: continue
  # Linear interpolation of the same-grid correlation removes the
  # nearest-node bias from the short finite-prime terms.
  fval=float(np.interp(lag,dx*np.arange(n),corr[c:]))
  term=lam/math.sqrt(nidx)*2*fval
  out += term; terms.append((nidx,term))
 return out,terms
def scan(r,K=24,dx=.0005):
 n=int(round(2*r/dx))+1;x=np.linspace(-r,r,n);m=np.ones(n)*dx;m[[0,-1]]=dx/2
 phase=np.pi*(x/r+1)/2;B=np.sin(np.arange(1,K+1)[:,None]*phase)
 A=np.stack([np.sum(m*B*np.exp(s*x),axis=1) for s in [0,.5,1]])
 U,s,Vh=np.linalg.svd(A,full_matrices=True);N=Vh[3:].T
 W=N.T@B;W=W/np.sqrt(np.sum(W*W*m[None,:],axis=1))[:,None] # not exact orth due cross
 # qr weighted
 Q,R=np.linalg.qr(W.T*np.sqrt(m[:,None])); F=np.linalg.solve(R,np.eye(R.shape[0])); W=F.T@W
 mom=np.stack([np.sum(m*W*np.exp(s*x)[None,:],axis=1) for s in [0,.5,1]])
 print('diag',r,'mom',np.max(np.abs(mom)),'gram',np.max(np.abs((W*m[None,:])@W.T-np.eye(W.shape[0]))))
 d=np.array([arch(W[i],dx) for i in range(W.shape[0])]);M=np.diag(d)
 for i in range(W.shape[0]):
  for j in range(i): M[i,j]=M[j,i]=(arch(W[i]+W[j],dx)-d[i]-d[j])/2
 ev=eigh((M+M.T)/2,eigvals_only=True)
 # Rebuild the top direction and read the actual finite-prime correction.
 vals,vecs=eigh((M+M.T)/2)
 top=vecs[:,-1]@W
 corr=fftconvolve(top[::-1],top,mode='full')*dx; c0=top.size-1
 qprime,terms=prime_sum(top,dx,r)
 # The actual IC gate is another quadratic form.  Reassemble it by
 # polarization on the same constrained orthonormal basis; this avoids
 # mistaking the Arch extremizer for the gate extremizer once primes enter.
 gd=np.array([arch(W[i],dx)+prime_sum(W[i],dx,r)[0] for i in range(W.shape[0])])
 G=np.diag(gd)
 for i in range(W.shape[0]):
  for j in range(i):
   gij=arch(W[i]+W[j],dx)+prime_sum(W[i]+W[j],dx,r)[0]
   G[i,j]=G[j,i]=(gij-gd[i]-gd[j])/2
 ge,gv=eigh((G+G.T)/2)
 gate_top=float(ge[-1])
 gfun=gv[:,-1]@W
 gdet=np.trapezoid(np.exp((.6+14.134725141734693j)*x)*gfun,x)
 det=np.trapezoid(np.exp((.6+14.134725141734693j)*x)*top,x)
 return ev[0],ev[-1],s,qprime,terms,det,ge[-1],gate_top,gdet
for K in [18,24]:
 for dx in [.001,.0005]:
  for r in [.6,.7,.8,.9,1.0]:
   a,b,s,qp,terms,det,gt,gg,gdet=scan(r,K=K,dx=dx)
   print('K',K,'dx',dx,'r',r,a,b,'prime_archtop',qp,
         'arch_gate',b+qp,'gate_top',gt,gg,'terms',terms,
         'archdet',det,'gatedet',gdet)
