import json
import numpy as np
from scipy.signal import fftconvolve
from math import log, pi

EULER=0.5772156649015329
C=log(4*pi)+EULER
LROOT=log(2)/2
RHO=0.6+14.134725141734693j

def bump(u):
    u=np.asarray(u,float); a=np.abs(u)
    out=np.zeros_like(a)
    core=a<=.9; out[core]=1.0
    tr=(a>.9)&(a<1)
    t=(a[tr]**2-.9**2)/(1-.9**2)
    q=np.exp(-1/t)/(np.exp(-1/t)+np.exp(-1/(1-t)))
    out[tr]=1-q
    return out

def direct_arch(f,dx, use_np=False):
    if use_np:
        corr=np.convolve(f[::-1],f)*dx
    else:
        corr=fftconvolve(f[::-1],f,mode='full')*dx
    n=f.size; c=n-1
    f0=float(corr[c])
    lags=dx*np.arange(1,c+1,dtype=float)
    fy=corr[c+1:]
    # stable compact-support integrand (F is even for autocorrelation)
    num=np.expm1(lags/2)*fy + (fy-f0)
    body=np.trapezoid(num/np.sinh(lags),lags)
    return C*f0+float(body), f0

def specs_for_basis():
    out=[]
    for w in [.025,.04,.06,.08]:
        for c in [-.25,-.18,-.10,0,.10,.18,.25]:
            if abs(c)+w < LROOT-.005: out.append((w,c))
    return out

def basis_grid(specs,dx):
    # exact symmetric grid, supports strictly inside +/- LROOT
    n=int(round(2*LROOT/dx))+1
    x=np.linspace(-LROOT,LROOT,n)
    B=np.array([bump((x-c)/w) for w,c in specs])
    return x,B

def arch_matrix(B,dx):
    m=B.shape[0]; q=np.zeros((m,m)); diag=np.zeros(m)
    for i in range(m):
        diag[i]=direct_arch(B[i],dx)[0]; q[i,i]=diag[i]
    for i in range(m):
        for j in range(i):
            # polarization, same direct evaluator
            qij=(direct_arch(B[i]+B[j],dx)[0]-diag[i]-diag[j])/2
            q[i,j]=q[j,i]=qij
    return (q+q.T)/2

def constraints(x,B):
    # trapezoid mass/Laplace constraints at 0,.5,1 and complex detection rho
    rows=[np.trapezoid(np.exp(s*x)[None,:]*B,x,axis=1) for s in [0.,.5,1.]]
    z=np.trapezoid(np.exp(RHO*x)[None,:]*B,x,axis=1)
    return np.vstack([rows[0],rows[1],rows[2],z.real,z.imag])

def nullspace(A,tol=1e-10):
    U,s,Vh=np.linalg.svd(A,full_matrices=True)
    rank=int(np.sum(s>tol*s[0]))
    return Vh[rank:].T,s,rank

def run(dx):
    specs=specs_for_basis(); x,B=basis_grid(specs,dx)
    Q=arch_matrix(B,dx); A=constraints(x,B)
    N,s,rank=nullspace(A)
    R=(N.T@Q@N); R=(R+R.T)/2
    ev,vec=np.linalg.eigh(R); v=N@vec[:,-1]
    target=np.array([0.,0.,0.,1.,0.])
    a0=A.T@np.linalg.solve(A@A.T,target)
    print(f'dx {dx:.8g} n {len(x)} basis {len(specs)} rank {rank} sv {s}')
    print('base residual',np.max(np.abs(A@a0-target)),'Q0',a0@Q@a0,'norm',np.linalg.norm(a0),'top null eig',ev[-1])
    rows=[]
    for t in [-10,-5,-3,-2,-1,0,1,2,3,5,10]:
        a=a0+t*v
        q=float(a@Q@a)
        print(' t',t,'Q',q,'norm',np.linalg.norm(a),'maxcoef',np.max(np.abs(a)), 'det',A[3:]@a)
        rows.append({'t':t,'Q_fft':q,'norm':float(np.linalg.norm(a)),
                     'maxcoef':float(np.max(np.abs(a))),
                     'det_re':float((A[3:]@a)[0]),
                     'det_im':float((A[3:]@a)[1])})
    # return coarse best t=5 for cross-grid
    vals=[(a0+t*v)@Q@(a0+t*v) for t in np.linspace(-10,10,401)]
    tb=float(np.linspace(-10,10,401)[int(np.argmax(vals))])
    # Independent direct convolution check for the normalized particular
    # solution and the extremal null direction.  This is deliberately a
    # value check, not a second matrix assembly: it catches correlation-index
    # mistakes such as the superseded 2168 F(0) reflection bug.
    for tag,a in [('a0',a0),('top_sample',a0+tb*v)]:
        f=np.sum(a[:,None]*B,axis=0)
        q_np=direct_arch(f,dx,use_np=True)[0]
        q_fft=direct_arch(f,dx,use_np=False)[0]
        print(' direct',tag,'Q_np',q_np,'Q_fft',q_fft,'absdiff',abs(q_np-q_fft))
        rows.append({'t':0 if tag=='a0' else tb,'tag':tag,
                     'Q_np':float(q_np),'Q_fft_combined':float(q_fft),
                     'absdiff':float(abs(q_np-q_fft))})
    return specs,a0+tb*v,tb,rows

if __name__=='__main__':
    artifact=[]
    for dx in [0.002,0.001]:
        specs,a,t,rows=run(dx)
        artifact.append({'dx':dx,'basis':len(specs),'rows':rows})
    with open('/home/peter/rh/results/2169_root_window_positive_candidate.json','w') as h:
        json.dump(artifact,h,indent=2)
