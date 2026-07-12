# Prolate Szego-Phase Prime-Coefficient Mechanism

Date: 2026-07-11

Status: exact source transfer phase and its prime-power coefficients obtained.
The theorem that the prolate cross-energy reads this phase remains open. RH
status is unchanged.

## 1. Purpose

The surviving pre-cutoff object is

```text
A_(S,lambda,g)=Pi_-(S,lambda) C_S(g) Pi_+(S,lambda),
Pos_(S,lambda,g)=norm(A_(S,lambda,g))_HS^2 >= 0.
```

The open question was whether the first Szego/scattering-phase correction of
the semilocal prolate projection can carry the exact finite-prime Weil
coefficient, rather than merely a periodic function of the right frequency.

## 2. First Variation Of The Polynomial Grading

For one prime put

```text
a=p^(-1/2),
L=log p,
w_a(s)=w_infinity(s)/|1-a exp(iLs)|^2.
```

At `a=0`,

```text
w_a(s)=w_infinity(s)(1+2a cos(Ls)+O(a^2)).                (F.1)
```

Let `(e_n)` be the archimedean orthonormal-polynomial basis and `N e_n=n e_n`.
Differentiating Gram--Schmidt along the fixed polynomial flag gives a
skew-adjoint infinitesimal basis change `K_L`:

```text
(K_L)_(m,n)
  = sign(m-n) <e_m,cos(LD)e_n>,

N'_0=[K_L,N].                                             (F.2)
```

For

```text
W_(a,lambda)=-D^2+2 pi lambda^2(4N_a+1)-1/4,
```

one gets

```text
W'_0=8 pi lambda^2 [K_L,N].                               (F.3)
```

Equations (F.1)--(F.3) are lower operator algebra. They use neither a Weil
sign nor a zero detector. The numerical file
`027_first_szego_variation_probe.py` implements this derivative using the
exact archimedean Jacobi coefficients. Finite Galerkin positive projections
show severe spectral pollution, so their values are not route evidence.

## 3. Exact Source Transfer Operator

CCM24 computes the semilocal Sonin transfer before scalar scattering
elimination. For `g=w_infinity(f)`, equations (58)--(59) give

```text
w_S(theta_S(f))(lambda)
  = g(lambda)-p^(-1/2)g(lambda/p).                         (F.4)
```

In the multiplicative Fourier coordinate this is the bounded outer multiplier

```text
B_p(s)=1-a exp(-iLs),
a=p^(-1/2),
L=log p.                                                  (F.5)
```

The scalar Euler scattering phase is the boundary-value ratio

```text
u_p(s)=B_p(-s)/B_p(s)
      =(1-a exp(iLs))/(1-a exp(-iLs)).                    (F.6)
```

Thus the arithmetic data needed by the prolate asymptotic already exists in
the pre-cutoff cyclic pair as a Szego outer function. It is not inserted as a
post-cutoff Dirac counterterm.

Primary source:

```text
CCM24 mainc2m24fine.tex:946-981, equations (58)--(59).
https://arxiv.org/abs/2310.18423
```

## 4. Exact Prime-Power Coefficients

Since `0<a<1`, the logarithm in (F.6) has an absolutely convergent expansion
with every derivative:

```text
log u_p(s)
  = -sum_(k>=1) a^k exp(ikLs)/k
    +sum_(k>=1) a^k exp(-ikLs)/k.
```

Therefore

```text
(1/(2i)) partial_s log u_p(s)
  = -L sum_(k>=1) a^k cos(kLs)                            (F.7)
```

up to the fixed Fourier/sign convention. Its absolute coefficients are

```text
log(p) p^(-k/2),                                          (F.8)
```

exactly those of the `p^k` and `p^(-k)` Weil atoms. This closes the local
coefficient calculation conditional only on one remaining interface: the
first subleading prolate/Christoffel--Darboux trace term must be the derivative
of the Szego phase (F.6).

### Rejected fixed-point shortcut

A bare real dilation fixed-point trace gives

```text
1/(p^(k/2)-p^(-k/2)),
```

not `p^(-k/2)`. Connes 1999 explicitly identifies this finite-iterate mismatch
when comparing a conventional periodic-orbit trace with the zeta explicit
formula. Do not multiply it by an unproved `1-p^(-k)` numerator. The valid
coefficient owner is the logarithmic derivative of the source transfer
function (F.5), not a bare archimedean fixed-point trace.

Source: Connes 1999, arXiv:math/9811068, Introduction formulas (6)--(7).

## 5. Remaining Global Theorem

The coefficient match does not prove that the whole cross-spectral trace has
the claimed limit. The next theorem must justify inserting (F.3) into the
spectral projection and identifying the subleading Szego phase:

```text
Pi'_+(0)
  = (1/(2 pi i)) integral_Gamma
      (z-W_0)^(-1) W'_0 (z-W_0)^(-1) dz,                 (F.9)

delta Pos_lambda(g)
  -> sum_(k>=1) log(p)p^(-k/2)
       ( <g,T_(p^k)g> + <g,T_(p^(-k))g> ).               (F.10)
```

Required controls:

```text
1. W_(S,lambda) is self-adjoint and zero is outside the contour Gamma,
   or threshold crossings are handled explicitly.

2. The resolvent-sandwiched FIO in (F.9) is trace class after the same
   C_S(g) smoothing used in Pos.

3. The Szego-phase expansion is summable in k and uniform as lambda grows.

4. The remainder tends to zero on the full common Weil form domain, not only
   for analytic vectors or a finite Jacobi section.

5. Higher orders in a assemble the exact logarithm of `B_p` rather than an
   unrelated nonlinear deformation. Formula (F.5) names the required answer,
   but the prolate trace still has to produce it.
```

The easiest rejection gate is item 5. Compute the second variation and check
that it equals the second Taylor coefficient of `log B_p`, including the
`p^(-1)` coefficient at the `p^2` atom. A mismatch rejects the proposed
Szego/prolate owner before any global semiclassical theorem is attempted.

## 6. Verdict

```text
old scalar-remainder coefficient: fatal Dirac'' term.
source Szego-phase coefficient: exact Weil coefficient.
prolate-to-Szego interface: open.
global positive-trace limit: open.
next attack: second variation / p^2 coefficient.
```
