# Proof 228: Euler chirp operator-norm compactness

Date: 2026-07-14

Status: exact new compactness theorem for the critical Euler endpoint channel.
The positive translated endpoint left by Proof 225 has a nondecaying
Hilbert--Schmidt norm after the Euler coefficient is inserted, but it is
unitarily equivalent to a truncated Fourier transform at frequency `p^m`.
Its operator norm is therefore `O(p^(-m/2))`.  The complete endpoint series,
including arbitrary fixed polynomial word weights, converges in operator norm
to a compact operator.  Thus non-summability of the termwise
Hilbert--Schmidt norms is not a route obstruction.  This does not prove the
interior-profile or full complete-crossing estimate `(F.23)` from Proof 227,
and it does not prove the three-row sign or RH.  No Lean owner is authorized.

## 1. The apparent endpoint obstruction

Proof 225 uses the exact archimedean response

```text
k_infinity(r)=2 exp(r/2) cos(2*pi*exp(r)).             (C.1)
```

For one prime, put

```text
L=log(p),
a=p^(-1/2),
q_m=mL.                                                (C.2)
```

The positive endpoint in the twice-integrated triangular asymptotic is
`k_infinity(r+q_m)`.  Multiplication by its Euler coefficient gives the exact
identity

```text
a^m k_infinity(r+q_m)
 =2 exp(r/2) cos(2*pi*p^m*exp(r)).                    (C.3)
```

The amplitude in `(C.3)` no longer decays with `m`.  Consequently its kernel
on a fixed interval has a Hilbert--Schmidt norm bounded away from zero.  It is
incorrect to try to sum those Hilbert--Schmidt norms.

The oscillation has simultaneously accelerated from frequency `1` to
frequency `p^m`.  The correct topology is operator norm.

## 2. Exact logarithmic chirp conjugation

Let `I=[A,B]` be any bounded real interval and define

```text
(K_lambda^+ f)(x)
 =integral_I exp((x-y)/2)
    exp(2*pi*i*lambda*exp(x-y)) f(y) dy,              (C.4)

lambda>0.
```

Put

```text
J=exp(I)=[exp(A),exp(B)],
J_inv=exp(-I)=[exp(-B),exp(-A)].                      (C.5)
```

The maps

```text
(U_I h)(u)=u^(-1/2)h(log u),       u in J,
(V_I f)(w)=w^(-1/2)f(-log w),      w in J_inv         (C.6)
```

are unitary from `L2(I,dx)` onto `L2(J,du)` and
`L2(J_inv,dw)`, respectively.  Indeed `du=u dx` and `dw=-w dy`
give the norm identities directly.

Set `u=exp(x)` and `w=exp(-y)` in `(C.4)`.  The half-density factors in
`(C.6)` cancel exactly, leaving

```text
(U_I K_lambda^+ V_I^(-1) g)(u)
 =integral_(J_inv) exp(2*pi*i*lambda*u*w) g(w) dw.
                                                               (C.7)
```

Thus the logarithmic chirp is not merely analogous to a Fourier transform.  It
is exactly a Fourier transform restricted to two finite intervals, followed
by the frequency dilation `xi=lambda*u`.

Extend `g` by zero outside `J_inv` and write

```text
g_hat(xi)=integral_R exp(2*pi*i*xi*w)g(w)dw.
```

Plancherel and `xi=lambda*u` give

```text
norm(K_lambda^+ f)_2^2
 =integral_J |g_hat(lambda*u)|^2 du
 <=lambda^(-1) integral_R |g_hat(xi)|^2 dxi
 =lambda^(-1) norm(f)_2^2.                            (C.8)
```

Therefore

```text
norm(K_lambda^+)<=lambda^(-1/2).                      (C.9)
```

The conjugate phase `K_lambda^-` has the same bound.  Hence the real chirp

```text
(C_lambda f)(x)
 =integral_I 2 exp((x-y)/2)
   cos(2*pi*lambda*exp(x-y)) f(y)dy                  (C.10)
```

satisfies

```text
norm(C_lambda)<=2 lambda^(-1/2).                      (C.11)
```

No asymptotic theorem is used in `(C.7)--(C.11)`; these are changes of
variables plus Plancherel.

## 3. Why Hilbert--Schmidt and operator norm disagree

Every `K_lambda^+` has a continuous kernel on `I x I`, so it is
Hilbert--Schmidt.  Its Hilbert--Schmidt norm is, however, independent of
`lambda`:

```text
norm(K_lambda^+)_HS^2
 =integral_(I x I) exp(x-y) dx dy.                    (C.12)
```

The phase disappears after taking the pointwise absolute value.  Formula
`(C.12)` explains the failed absolute-Hilbert--Schmidt strategy exactly:

```text
termwise HS norms:       constant, not summable;
termwise operator norms: O(lambda^(-1/2)), summable at lambda=p^m.          (C.13)
```

This is not a contradiction.  Increasing oscillation spreads the singular
values across more directions while decreasing the largest one.

## 4. Norm-convergent Euler endpoint series

Set `lambda=p^m` in `(C.11)`.  Identity `(C.3)` says that the critical positive
endpoint operator is exactly `C_(p^m)`.  Therefore

```text
norm(C_(p^m))<=2p^(-m/2).                             (C.14)
```

For every fixed nonnegative integer `r`,

```text
sum_(m>=1) m^r norm(C_(p^m))
 <=2 sum_(m>=1)m^r p^(-m/2)
 <infinity.                                           (C.15)
```

Each partial sum is compact because every summand is Hilbert--Schmidt.  The
compact operators are closed in operator norm, so `(C.15)` proves:

```text
sum_(m>=1)m^r C_(p^m) is compact on L2(I).            (C.16)
```

An interpolation series with coefficient `a^(m-1)` instead of `a^m` differs
only by the fixed factor `sqrt(p)` and has the same conclusion.

The other two endpoint orientations are easier.  Directly from `(C.1)`:

```text
a^m k_infinity(r-q_m)
 =2p^(-m)exp(r/2)cos(2*pi*p^(-m)*exp(r)),             (C.17)
```

so their Hilbert--Schmidt norms are geometrically summable.  Terms at the
fixed center `r=0` also retain the geometric factor `a^m`.  Hence the complete
three-endpoint contribution in Proof 225's formula `(T.8)` is compact after
Euler summation.

## 5. What this changes in Proof 227

The critical endpoint was the only part whose Euler coefficient exactly
canceled the archimedean amplitude `exp(q_m/2)`.  Formula `(C.16)` proves that
this cancellation does not create a noncompact channel: the matching phase
acceleration supplies an additional `p^(-m/2)` operator-norm gain.

Therefore the following implication is false:

```text
nondecaying local L2/HS kernel size
  => noncompact Euler sum.                             (C.18)
```

For the complete flow owner

```text
Y_alpha
 =(I-E_alpha)X_alpha B_alpha
   -R_alpha X_alpha*B_alpha,                          (C.19)
```

the remaining task is narrower:

```text
identify the internal, non-endpoint profile of the complete difference;
put every surviving high-frequency term into a logarithmic chirp form;
prove uniform bounded-amplitude control before applying (C.9).             (C.20)
```

Proof 228 establishes the sharp norm mechanism needed for the last step.  It
does not assert that every internal term in `(C.19)` already has the required
amplitude control.

## 6. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/228_euler_chirp_operator_norm_compactness.py
python3 -B docs/proofs/228_euler_chirp_operator_norm_compactness.py \
  --prime 3 --modes 5
```

The deterministic Nyström certificate checks:

```text
the exact positive and negative endpoint identities (C.3), (C.17);
the bound norm(K_(p^m)^+)<=p^(-m/2);
the nondecaying Hilbert--Schmidt norm (C.12);
the convergence of polynomially weighted analytic norm bounds.
```

The discretization is evidence for the scaling law, not its proof.  The proof
is the exact unitary conjugation `(C.6)--(C.9)`.

## 7. Route judgment

```text
logarithmic chirp Fourier conjugation:        exact
critical endpoint operator norm:              <=p^(-m/2) per phase
critical endpoint Hilbert--Schmidt norm:       nondecaying
polynomially weighted Euler endpoint sum:      compact in operator norm
HS-absolute-summability requirement:           rejected as unnecessary
complete internal profile / Proof 227 (F.23):  open
integrated three-row sign:                     open
Lean owner or route rewire:                    none
RH:                                            unproved
```

The next proof should apply `(C.9)` after deriving the full internal profile of
the same-object crossing `(C.19)`.  Returning to termwise Hilbert--Schmidt
summation would discard the oscillatory gain proved here.
