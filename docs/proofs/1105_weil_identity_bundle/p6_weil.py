"""P-6: Weil-identity matrix test.
HYPOTHESIS (pre-registered before running):
  On the triple-vanishing window space V, with compact support killing all
  invisible prime terms and the moment constraints killing all pole terms,
  the Weil explicit formula degenerates to the EXACT operator identity
      M := A + P  =  kappa * Z,
      Z_ij = 2 * sum_{j: ordinate gamma_j of nontrivial zeros} Re(v_ji * conj(v_jj')),
      v_ji = Simpson-integral of f_i(t) * exp(i * gamma_j * t) dt.
  (Centered-convention reading: Phi_c(rho) = M(i*gamma)*M(-i*gamma) = |g_hat(gamma)|^2
  for RH zeros; kappa = +-1 or +-2 from convention constants; the fit decides.)
"""
import time
import numpy as np
import math
from f0 import null_setup, arch_matrix, prime_matrix, simpson
from scipy.linalg import eigh
from mpmath import zetazero

def zero_gram(a, K, Nz=60, n=4001, tail=True):
    t, h, coeffs, basis = null_setup(a, K, n)
    funcs = coeffs.T @ basis
    d = funcs.shape[0]
    A = arch_matrix(funcs, h)
    P = prime_matrix(funcs, coeffs, basis, t, h, a, K)
    M = A + P
    quad = simpson(n, h)
    gam = np.array([float(zetazero(k).imag) for k in range(1, Nz + 1)])
    V = np.zeros((Nz, d)); Vi = np.zeros((Nz, d))
    for j, g in enumerate(gam):
        V[j] = (quad * np.cos(g * t)) @ funcs.T
        Vi[j] = (quad * np.sin(g * t)) @ funcs.T
    Vc = V + 1j * Vi
    Zd = (Vc.conj().T @ Vc).real * 2.0    # Hermitian Gram, 2 = both signs of gamma
    Zt = np.zeros((d, d))
    if tail:   # density tail beyond gamma_Nz: 2*int N'(u)|m(u)|^2 du
        ug = np.linspace(gam[-1], 400.0, 2401)
        dens = (np.log(ug / (2 * math.pi)) - 1.0) / (2 * math.pi)
        accR = np.zeros((len(ug), d)); accI = np.zeros((len(ug), d))
        for k, u in enumerate(ug):
            accR[k] = (quad * np.cos(u * t)) @ funcs.T
            accI[k] = (quad * np.sin(u * t)) @ funcs.T
        Mc = accR + 1j * accI
        GramU = np.einsum('ki,kj->ij', Mc, Mc.conj()).real
        for i in range(d):
            for j in range(d):
                Zt[i, j] = 2.0 * np.trapezoid(dens * GramU[i, j], ug)
    Z = Zd + Zt
    return dict(a=a, K=K, d=d, t=t, h=h, funcs=funcs, A=A, P=P, M=M,
                gam=gam, Z_discrete=Zd, Z_tail=Zt, Z=Z, Vc=Vc)

def report(a, K, Nz=60):
    r = zero_gram(a, K, Nz=Nz)
    M, Z, A = r["M"], r["Z"], r["A"]
    Zd, Zt = r["Z_discrete"], r["Z_tail"]
    nA = np.linalg.norm(A)
    kap = float(np.sum(M * Z) / np.sum(Z * Z))
    resid = np.linalg.norm(M - kap * Z) / nA
    ev = lambda m: eigh((m + m.T) / 2.0, eigvals_only=True)
    evM, evZ = ev(M), ev(kap * Z)
    kap_d = float(np.sum(M * Zd) / np.sum(Zd * Zd))
    resid_d = np.linalg.norm(M - kap_d * Zd) / nA
    print(f"--- P-6 (a={a}, K={K}, dim V = {r['d']}, zeros used = {Nz}+tail) ---")
    print(f"||A||_F = {nA:.4f}   ||M||_F = {np.linalg.norm(M):.2e}   "
          f"||Z||_F = {np.linalg.norm(Z):.2e}   ||Z_tail||/||Z|| = "
          f"{np.linalg.norm(Zt)/max(np.linalg.norm(Z),1e-30):.1e}")
    print(f"best kappa (M = kappa*Z): {kap:+.4f}    residual ||M-kappa*Z||/||A|| = {resid:.2e}")
    print(f"discrete-only kappa: {kap_d:+.4f}    residual: {resid_d:.2e}")
    print(f"eigs(M)        : {np.array2string(evM, precision=6, max_line_width=100)}")
    print(f"eigs(kappa*Z)  : {np.array2string(evZ, precision=6, max_line_width=100)}")
    print(f"top(M) = {evM[-1]:+.3e}   kappa*lambda_min(Z) = {kap*ev((Z))[0]:+.3e}")
    print(f"lambda_min(M) = {evM[0]:+.6f}   kappa*lambda_max(Z) = {kap*ev(Z)[-1]:+.6f}")
    vn = np.linalg.norm(r["Vc"], axis=1)
    print("|v_j| for j=1..10 : " + " ".join(f"{x:.2e}" for x in vn[:10]))
    print()
    return r

if __name__ == "__main__":
    t0 = time.time()
    report(2.0, 8); report(4.0, 8); report(2.0, 16)
    print("elapsed %.1fs" % (time.time() - t0))
