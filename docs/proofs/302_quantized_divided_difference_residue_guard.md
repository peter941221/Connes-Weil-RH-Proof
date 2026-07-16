# Proof 302: Quantized divided differences and the post-Q residue guard

Date: 2026-07-16

Status: source-backed correction of Proof 301's proposed contour successor.
CC20's pre-`Q` trace remainder has the expected half-power tail, but the
operator `Q=-(rho partial_rho)^2+1/4` creates a separate `-2 Dirac_0` residue
and an oscillatory regular tail.  A global post-`Q` `exp(-z/2)` strip estimate
is therefore false.  CC20's Appendix D/E instead supplies the correct local
owner: a quantized differential (quantized differential) whose kernel is a
divided difference `(f(s)-f(t))/(s-t)`.  This is exactly compatible with Proof
301's two-point covariance and removes the diagonal singularity before any
trace estimate.

This does not prove the combined moving `E/R/K_prol` estimate, Gate 3U, the
finite-`S` sign, the arithmetic same-object identity, negative-owner
integration, Burnol's all-zero identity, or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| CC20 pre-Q delta half-power                   | retained                     |
| derivative jump at rho=1                     | exact source mechanism       |
| post-Q distribution split                     | -2 Dirac_0 + regular        |
| global post-Q half-power tail                 | rejected                    |
| quantized divided-difference kernel           | exact source formula        |
| diagonal finite-difference singularity        | removable                   |
| outer quantized-calculus channel              | source-backed architecture   |
| combined moving E/R/K_prol estimate           | open                         |
| Gate 3U and RH                                | unproved                     |
+------------------------------------------------+------------------------------+
```

The route correction is

```text
Proof 301 contour shift of Q(delta/epsilon)
  -> isolate the universal -2 Dirac_0 residue
  -> use CC20 quantized differential [H,f]
  -> represent every legal detector by a divided difference
  -> recombine E/R/K_prol before estimating                 (BM.1)
```

The first three arrows are source-backed.  The final combined estimate remains
the hard theorem.

## 2. CC20 delta before and after Q

CC20 formula `(10)` (source label `sch18intro`) gives, for `rho>=1`,

```text
delta(rho)
 =2 sqrt(rho) [
    Si(2 pi(1+rho))/(2 pi(1+rho))
   +Si(2 pi(rho-1))/(2 pi(rho-1))].                   (BM.2)
```

The inversion symmetry is

```text
delta(rho^(-1))=delta(rho).                           (BM.3)
```

Consequently `d(x)=delta(exp(|x|))` is even.  Direct differentiation of
`(BM.2)` gives

```text
delta'(1+)=1,
d'(0+)=1,
d'(0-)= -1.                                         (BM.4)
```

The derivative jump is therefore `2`.  In logarithmic coordinates,

```text
Q_+=-partial_x^2+1/4,
Q_+ d = -2 Dirac_0 + q_reg.                           (BM.5)
```

For `rho>1`, differentiating `(BM.2)` away from the diagonal gives the regular
part

```text
q_reg(rho)
 =-4 rho^(3/2) A'(rho)
  -2 rho^(5/2) A''(rho),                              (BM.6)

A(rho)=Si(2 pi(1+rho))/(2 pi(1+rho))
         +Si(2 pi(rho-1))/(2 pi(rho-1)).
```

Equation `(BM.5)` is the distributional statement already recorded in the
project's CC20 source bridge.  The Dirac term is not part of the ordinary
continuous kernel on the diagonal and cannot be silently absorbed into it.

## 3. Why the global strip target fails

Before `Q`, the sine-integral asymptotics give

```text
sqrt(rho) |delta(rho)| = O(1).                        (BM.7)
```

After `Q`, the powers of `rho` in `(BM.6)` multiply the oscillatory sine
integral derivatives.  A global bound of the form

```text
|q_reg(exp(z))| <= C exp(-z/2)                        (BM.8)
```

is false.  The default certificate evaluates

```text
rho=1024:
|q_reg(rho)| approximately 128.0004,
sqrt(rho)|q_reg(rho)| approximately 4096.
```

The alternate cohort at `rho=2048` gives a rejection ratio approximately
`8192`.  These are direct evaluations of the source formula, not finite
matrix boundary artifacts.

The correct weak distribution identity is tested against a compact even bump
`phi`:

```text
integral_R d(x)(-phi''(x)+phi(x)/4) dx
 =-2 phi(0)+integral_R q_reg(exp(|x|)) phi(x) dx.      (BM.9)
```

The two cohorts have numerical quadrature errors `5.12e-11` and `2.71e-10`.
Thus the failure of `(BM.8)` is structural: the residue and regular tail are
separate source objects.

This corrects Proof 301's provisional successor.  A contour shift may be
applied only after the residue has been explicitly paired with the matching
diagonal term; it cannot be applied to `Qdelta` or `Qepsilon` as if they were
globally decaying functions.

## 4. CC20's quantized divided difference

CC20 Appendix D defines

```text
H=2 Fourier 1_[0,infinity) Fourier^(-1)-1,
^{-}d f=[H,f].                                        (BM.10)
```

For a Schwartz multiplier `f`, Appendix D gives the source kernel

```text
([H,f])(s,t)
 =i/pi * (f(s)-f(t))/(s-t).                           (BM.11)
```

Appendix E gives the same formula for the logarithmic derivative of the
archimedean scattering multiplier `u(s)=exp(2 i theta(s))`.  The key feature is
not the value on the diagonal but the divided difference:

```text
lim_(t->s) (f(s)-f(t))/(s-t)=f'(s).                  (BM.12)
```

Therefore a smooth detector has no diagonal singularity after the commutator
is formed.  Constants vanish exactly:

```text
^{-}d 1=0.                                            (BM.13)
```

For two multipliers `f,g`, the finite-dimensional kernel calculation gives

```text
Tr(([H,f])^* [H,g])
 =sum_(s,t) conjugate(K_f(s,t)) K_g(s,t),             (BM.14)
```

with `K_f,K_g` the divided differences in `(BM.11)`.  This is the same
two-point finite-difference mechanism as Proof 301 `(BL.3)`, now tied to a
source operator rather than an abstract projection matrix.

The certificate checks, in two matrix cohorts,

```text
divided-difference kernel error       <3e-16,
double-pairing readback error         <9e-16,
constant-mode commutator              exactly zero,
removable diagonal error              1.4e-12.         (BM.15)
```

These finite matrices certify the source kernel algebra.  They do not claim
that the whole Euler multiplier is identity plus trace class.

## 5. Consequence for the moving Sonin owner

At synchronized time `alpha`, Proof 301 supplies the legal root-paired scalar

```text
S_(E_alpha,R_alpha)(w,h_alpha)
 =<F_(eta,xi),
    A_(E_alpha)(.,h_alpha)-A_(R_alpha)(.,h_alpha)>,   (BM.16)
```

where `h_alpha=Re(T_alpha' T_alpha^(-1))`.  The CC20 identity

```text
R_alpha=E_alpha E_hat_alpha E_alpha-K_prol,          (BM.17)
```

must be inserted before applying `(BM.11)`.  The resulting scalar has three
physical pieces:

```text
outer divided-difference crossing
  + second-support/scattering divided-difference crossing
  + prolate trace-class commutator.                    (BM.18)
```

The universal `-2 Dirac_0` term is a diagonal form contribution, not a fourth
positive branch.  Keep it paired with the ordinary regular term through the
same compact root.  Deleting it or estimating the regular term alone changes
the source form.

The corrected analytic target is therefore

```text
|2 integral_0^1
   <F_(eta,xi), A_(E_alpha,R_alpha)(.,h_alpha)> d alpha|
 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r),                     (BM.19)
```

with `(BM.11)` used to define the completed crossings and `(BM.17)` kept whole.
The remaining source theorem is a divided-difference/Sonin estimate, not a
global decay estimate for `Qdelta`.

## 6. Finite certificate

`302_quantized_divided_difference_residue_guard_probe.py` verifies:

```text
CC20 delta derivative jump and inversion symmetry;
the weak `-2 Dirac_0 + q_reg` split;
pre-Q half-power versus post-Q rejection;
the quantized divided-difference kernel;
double-pairing readback and constant-mode cancellation.              (BM.20)
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/302_quantized_divided_difference_residue_guard_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/302_quantized_divided_difference_residue_guard_probe.py \
  --maximum-rho 2048 --test-radius 2.4 --matrix-size 44 \
  --quadrature-order 1000
```

The two cohorts report:

```text
+--------------------------------------------+-------------+-------------+
| diagnostic                                 | default     | alternate   |
+--------------------------------------------+-------------+-------------+
| maximum exact error                        | 5.12e-11    | 2.71e-10    |
| pre-Q sqrt(rho) delta magnitude            | 0.99990     | 0.99995     |
| post-Q half-power rejection ratio          | 4096        | 8192        |
| divided-difference kernel error            | 2.40e-16    | 2.98e-16    |
| double-pairing error                       | 0           | 8.88e-16    |
| constant-mode commutator                  | 0           | 0           |
+--------------------------------------------+-------------+-------------+
```

The large post-`Q` ratios are rejection evidence, not a numerical estimate of
the route response.

## 7. Route judgment

```text
naive global Qdelta strip:       rejected;
unpaired Dirac deletion:         forbidden;
quantized divided difference:    source-backed owner;
combined E/R/K_prol estimate:    open;
Gate 3U and RH:                  open / unproved.       (BM.21)
```

The primary source is CC20, *Weil positivity and Trace formula, the
archimedean place*, arXiv:2006.13771:

```text
https://arxiv.org/abs/2006.13771
```

The local project bridges recording the same source facts are
`docs/proofs/160_cc20_source_kernel_haar_bridge.md` and
`docs/proofs/171_cc20_qdelta_branch_derivative_reduction.md`.  Proof 302 adds
the ownership correction connecting those facts to Proof 301's moving
two-point kernel.  No Lean route consumer is changed.

## 8. Successor: Proof 303

Proof 303 now closes the finite source-shaped bridge for the full moving
`E/R/K_prol` kernel.  Its Hardy commutator readback and branch expansion are
exact at every sampled transport time, while deletion of `K_prol` changes the
signed scalar.  The separate `-2 Dirac_0` ledger is not recovered by the
ordinary divided-difference matrix; automatic cancellation is therefore
rejected rather than assumed.

Proof 304 now constructs the ordinary residue-augmented owners
`K_I - 2 Id` and `K_window - 2 P_window`, proves their exact zero-extension
quadratic identity, and rewires finite natural-Mellin control to those named
objects.  This closes carrier and diagonal bookkeeping only.  The next hard
point is the continuous root-sandwiched `E/R/K_prol` bridge and its
same-test compatibility, before any contour or Sobolev estimate.  See
`docs/proofs/304_cc20_quantized_remainder_owner.md`.
