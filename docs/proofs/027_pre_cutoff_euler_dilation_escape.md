# Pre-Cutoff Euler-Dilation Escape

Date: 2026-07-11

Status: two natural escapes and the finite-cutoff exact-read-off version are
rejected. One asymptotic source-backed candidate survives. RH status is
unchanged.

## 1. Route Obligation

The direct scalar scattering remainder is rejected because the pure finite
place contributes

```text
D_p = sum_k d_k Dirac_(k log p),
d_0 = p^(-1) log p > 0.
```

After `Q=-partial^2+1/4`, this produces an unbounded second-order point
interaction. A valid escape must therefore form its positive trace before the
finite local channel is eliminated to the scalar phase `u_p`.

```text
old weak path: scalar u_S -> support compression -> D_S o Q
new owner: full semilocal cyclic pair before scalar scattering elimination
forbidden input: sign(D_S), source RH, detector coverage
first rejection guard: no Dirac'' term in the new trace read-off
```

## 2. Rejected Escape: theta/eta Biorthogonal Trace

CCM24 proves

```text
Fourier_S theta_S = theta_S Fourier_infinity,
<theta_S f, eta_S g> = <f,g>.
```

The second identity makes `theta_S` and `eta_S` dual similarities. An
archimedean positive trace can therefore be transported as a paired trace,
with the two similarities cancelling. But CCM24 also proves

```text
upsilon_S theta_S(f) = upsilon_infinity(f).
```

Thus the same cancellation removes every finite Euler factor. The transported
trace reads only the archimedean Weil term, not the semilocal Weil form.

Verdict: positivity survives, arithmetic visibility does not. Rejected.

Source: CCM24 `mainc2m24fine.tex:978-1020`, especially equations (59) and
`upsilon_S theta_S=upsilon_infinity`.

## 3. Rejected Escape: Naive Graded Euler Supertrace

Put `a=p^(-1/2)` and `z=exp(is log p)`. The finite Euler phase factors as

```text
u_p(z) = z / B_a(z),
B_a(z) = (z-a)/(1-a z).
```

Both `z` and `B_a` are degree-one inner functions. Replacing the scalar
quotient by the graded pair `diag(z,B_a)` cancels the equal winding defects,
so its supertrace has no central second-order Dirac term. This is the exact
algebraic cancellation sought from a pre-cutoff dilation.

It does not preserve positivity. In the Hardy model, the two defect spaces are

```text
K_z   = span{1},
K_Ba  = span{k_a},
k_a(z)=sqrt(1-a^2)/(1-a z).
```

Their normalized overlap is

```text
|<1,k_a>| = sqrt(1-a^2).
```

Hence the difference of the two rank-one defect projections has eigenvalues

```text
eigenvalues(P_Kz-P_KBa) = {+a,-a} = {+p^(-1/2),-p^(-1/2)}.
```

The local cancellation is therefore intrinsically indefinite. Calling its
supertrace positive would store the missing theorem in the grading.

Verdict: arithmetic visibility survives, ordinary positivity does not.
Rejected.

## 4. Surviving Escape: Semilocal Prolate Spectral Projection

CCM24 explicitly proposes a different pre-cutoff mechanism. For the semilocal
cyclic pair `(Scaling,xi_S)`, its spectral measure is

```text
dm_S(s) = |product_(v in S) L_v(1/2-is)|^2 ds.
```

The associated orthogonal-polynomial grading `N_S` gives the formal prolate
operator

```text
W_(S,lambda)
  = -Scaling^2 + 2 pi lambda^2 (4 N_S+1) - 1/4.           (P.1)
```

The proposed mechanism is to replace finite-codimension conditioning by the
orthogonality of the positive and negative spectral subspaces of (P.1). This
happens before reduction to the scalar scattering phase, so the death proof
for `D_p` does not automatically apply.

Primary evidence:

```text
CCM24 mainc2m24fine.tex:185-205
  states the positive-trace/Weil comparison strategy and automatic spectral
  conditioning.

CCM24 mainc2m24fine.tex:232-255
  constructs the semilocal cyclic pair and its Euler-weighted measure.

CCM24 mainc2m24fine.tex:259-270
  calls the prolate construction a candidate, keeps domain issues formal,
  and defers a second adelic Weil-representation candidate.
```

URL: https://arxiv.org/abs/2310.18423

The 2024 follow-up computes the `S={infinity,p}` moments and Jacobi
deformation, but does not prove the positive trace comparison needed here.

URL: https://arxiv.org/abs/2403.01247

## 5. Finite-Cutoff Exact Read-Off Is Impossible

Let `Pi_+(S,lambda)` be the positive spectral projection of a proved
self-adjoint realization of (P.1), and put `Pi_-=1-Pi_+`. For one compact
source test `g`, define the cross-spectral transition

```text
A_prol(S,lambda,g)
  = Pi_-(S,lambda) C_S(g) Pi_+(S,lambda),

Pos_prol(S,lambda,g)
  = Tr(A_prol* A_prol)
  = norm(A_prol)_HS^2 >= 0.                              (P.2)
```

For self-adjoint `C_S(g)`, this is one half of the commutator energy

```text
norm([Pi_+(S,lambda),C_S(g)])_HS^2.
```

Using `Pi_+ C_S(g) Pi_+` instead is rejected: its growing rank creates a bulk
trace divergence whose subtraction destroys the automatic positivity. The
cross-spectral object (P.2) is exactly the implementation of the source's
positive/negative spectral orthogonality and has no rank bulk.

Assume, as in the classical prolate case, that `Pi_+(S,lambda)` has finite
rank. Matrix coefficients of the strongly continuous scaling representation
are continuous. Consequently the bilinear kernel of (P.2) is continuous at
every finite cutoff; schematically its diagonal coefficient is built from

```text
kappa_(S,lambda)(r)
  = Tr(Pi_+(S,lambda) U(-r) Pi_-(S,lambda)
                       U(r) Pi_+(S,lambda)).              (P.3)
```

This is a continuous function of `r`. Consequently a finite-rank prolate
compression cannot exactly produce the prime-power point masses in the Weil
functional at `r=k log p`. Any exact finite-cutoff equation must put those
point masses back into its remainder, reproducing the obstruction it was
meant to remove.

Verdict: exact finite-cutoff `Pos_prol=QW+compact remainder` is rejected by
regularity, independently of numerics.

## 6. Surviving Asymptotic Contract

The only possible read-off is distributional convergence as the prolate
cutoff grows:

```text
kappa_(S,lambda) -> kappa_Weil,S
                     in the common Weil form dual,         (P.4)

Pos_prol(S,lambda,g)
  = QW_smooth,S,lambda(g,g) + R_prol,S,lambda(g),          (P.5)

QW_smooth,S,lambda(g,g) -> QW_S(g,g),
R_prol,S,lambda(g) -> 0.                                  (P.6)
```

The mandatory properties are:

```text
finite Euler atoms appear only as limits of continuous kernels
convergence holds on one common unbounded Weil form domain
the same compact test g occurs in positivity and in the limit
no detector theorem or RH-level sign premise
```

This genuinely bypasses the fixed-`lambda` Dirac-double-prime obstruction: no
distributional point mass is differentiated at a finite stage. Its price is
that (P.4)--(P.6) now own the whole arithmetic convergence theorem.

## 7. Why Prime Powers Can Reappear In The Limit

The semilocal measure is an analytic multiplicative perturbation of the
archimedean measure:

```text
dm_S(s)=dm_infinity(s) product_(p in S_f) |L_p(1/2-is)|^2,

log |L_p(1/2-is)|^2
  = 2 sum_(k>=1) p^(-k/2) cos(k s log p)/k.                (P.7)
```

In strong asymptotics of orthogonal polynomials, such a nonvanishing analytic
weight perturbation enters the subleading Christoffel--Darboux kernel through
its Szego/scattering phase. Differentiating the phase in (P.7) supplies the
missing factor `log p`; its Fourier modes are exactly the prime powers
`p^k`. This gives a concrete mechanism by which continuous finite-cutoff
kernels can concentrate onto the finite-prime Weil atoms in (P.4).

This mechanism is an inference, not a theorem currently supplied by CCM24.
The closest general results found cover bulk universality or periodically
modulated Jacobi parameters, but not the required global subleading trace
asymptotic for this unbounded exponential weight:

```text
Swiderski--Trojan, Christoffel--Darboux kernels for periodically modulated
Jacobi parameters, arXiv:1909.09107.

Lukic, bulk universality from Weyl m-functions, arXiv:2108.01629.

Yafaev, Jacobi scattering and Bernstein--Szego asymptotics,
arXiv:1711.05029 (trace-class perturbations of the free Jacobi operator).
```

The project needs a stronger theorem: retain the first Szego-phase correction,
insert it into the cross-spectral Hilbert--Schmidt energy, and control the
error uniformly on the common Weil form domain.

## 8. Numerical Screen

`027_semilocal_prolate_kernel_probe.py` constructs finite Jacobi sections for
`S={infinity,2}` from the Euler-weighted measure and evaluates the actual
cross-spectral translation energy

```text
E(r)=norm(Pi_- U(r) Pi_+)_HS^2.
```

It gives `E(0)=0` to numerical precision, confirming the absence of the rank
bulk. At `lambda=0.5` and `r=log 2`, the unnormalized values are approximately

```text
section 16: 1.3316
section 24: 1.3759
section 32: 1.4746
```

This is more stable than the rejected diagonal compression, but it is not a
convergence result. Finite Jacobi truncation still has spectral pollution near
the positive threshold, especially at larger `lambda`. No route judgment is
based on these numbers.

## 9. Remaining Death Gates

```text
P0  self-adjoint realization of W_(S,lambda)
    Source status: formal; likely analytic, not yet a route theorem.

P1  cross-spectral transition is Hilbert-Schmidt on the same source test
    Source status: not supplied.

P2  first Szego-phase correction gives the prime-power coefficients
    Source status: structurally matched by (P.7), but no covering theorem.

P3  common-domain distributional convergence (P.4)--(P.6)
    Source status: not supplied; this is now the main mathematical bottom.

P4  projected family remains sufficient for the CC20/Weil RH exit
    Source status: could become RH-level if stated as detector coverage.
```

## 10. Decision

```text
theta/eta paired transport: dead, loses finite arithmetic.
naive Euler supertrace: dead, loses positivity by eigenvalues +/-p^(-1/2).
semilocal prolate positive projection: alive but unproved.
finite-cutoff exact prolate read-off: dead by continuity versus prime atoms.
asymptotic prolate read-off: alive; main gate is common-domain convergence.
prime-power mechanism: Szego-phase modes match the required p^k and log p.
next attack: derive or reject the first Szego-phase correction to (P.2),
without using finite-section eigenvalue convergence as a substitute.
```

This is a real change of object, not a new estimate on the rejected `D_S`.
No Lean owner should be introduced until P2 passes.
