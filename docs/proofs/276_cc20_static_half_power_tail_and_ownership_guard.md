# Proof 276: CC20 static half-power tail and first-jet ownership guard

Date: 2026-07-15

Status: source-backed tail theorem and same-object guard.  CC20's explicit
archimedean trace remainder `delta(rho)` is `O(rho^(-1/2))`.  More importantly,
CC20's prolate expansion of the Sonin correction `epsilon(rho)`, together with
its explicit rapid eigenvalue decay and polynomial prolate Sobolev bounds,
gives

```text
epsilon(rho)=O(rho^(-1/2)(1+log(rho))),  rho>=2.       (AM.1)
```

Thus the exact `exp(-z/2)` scale requested by Proof 275 is already present in
the static CC20 remainder when `rho=exp(z)`.

This does not prove Proof 275 `(AL.17)`.  The CC20 function `epsilon` is the
static difference between the archimedean Weil distribution and the Sonin
trace.  Proof 275's `q_R` is a moving-projection Dirichlet first jet.  No source
identity currently identifies those two objects after the route's `Q` root,
three physical branches, and renewal are inserted.  Gate 3U and RH remain
open.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| CC20 explicit delta formula                   | source-backed                |
| delta(rho)=O(rho^(-1/2))                      | proved                       |
| CC20 epsilon prolate expansion                | source-backed                |
| epsilon(rho)=O(rho^(-1/2)(1+log rho))         | proved                       |
| regular W_infinity tail                       | O(rho^(-1/2)), source formula|
| full static Sonin coefficient tail            | half-power plus one log      |
| polynomially weighted prolate sum             | absolutely convergent        |
| epsilon equals Proof 275 moving first jet      | not proved / do not assume   |
| large-rho Q epsilon bound                      | open                         |
| determinant-resummed mixed renewal             | open                         |
| Gate 3U and RH                                 | unproved                     |
+------------------------------------------------+------------------------------+
```

The ownership diagram is

```text
CC20 static trace remainder
  -> correct half-power tail exp(-z/2)
  -> candidate source mechanism
  -X-> moving semilocal first jet without a new identity.        (AM.2)
```

## 2. The explicit `delta` tail

CC20 equation `(10)`, source label `sch18intro`, gives for `rho>=1`

```text
delta(rho)
 =2 rho^(1/2) [
    Si(2 pi(1+rho))/(2 pi(1+rho))
   +Si(2 pi(rho-1))/(2 pi(rho-1))].                  (AM.3)
```

The sine integral `Si` is bounded on the positive real axis.  For `rho>=2`,

```text
|delta(rho)|
 <=C rho^(1/2)[1/(rho+1)+1/(rho-1)]
 <=C' rho^(-1/2).                                     (AM.4)
```

CC20 also proves `delta(rho^-1)=delta(rho)`.  With `rho=exp(z)`, `(AM.4)` is

```text
|delta(exp(z))|<=C exp(-z/2).                         (AM.5)
```

The probe evaluates `(AM.3)` directly.  The scaled quantity
`sqrt(rho)|delta(rho)|` tends numerically to `1`, in agreement with the two
`Si` limits.  The proof of `(AM.4)` uses only boundedness of `Si`.

## 3. CC20's exact Sonin correction

Let `xi_n` be CC20's normalized even prolate vector supported in `[0,1]`, set

```text
eta_n=Fourier(xi_n),
zeta_n=P eta_n/sqrt(1-lambda_n^2),
tau_n=lambda_n/sqrt(1-lambda_n^2).                    (AM.6)
```

CC20 Theorem `devil`, equations `sonine1` and `sonine0`, proves

```text
Tr(theta(f) S)
 =W_infinity(f)+integral f(rho^-1)epsilon(rho)d*rho,

epsilon(rho)
 =sum_n tau_n <xi_n,theta(rho^-1)zeta_n>,  rho>=1.    (AM.7)
```

The same source proves

```text
|lambda_n|
 <=2^(2n) pi^(2n+1/2) ((2n)!)^2
   /[(4n)! Gamma(2n+3/2)],                            (AM.8)
```

which is super-exponentially small, and supplies polynomial bounds for the
prolate endpoint and Sobolev quantities.  In the source notation:

```text
|xi_n(1)|<=sqrt(2n+1/2),

||(1-x^2)xi_n''||_2<=C(1+n)^2,

||D_u xi_n||_2<=C(1+n)^2.                             (AM.9)
```

These are source equations `Rokh`, `boundWang`, and the displayed estimate
following `boundWang`.

## 4. Derive the `epsilon` half-power tail

The estimates in `(AM.9)` imply a polynomial bounded-variation estimate

```text
||xi_n||_infinity+||xi_n'||_1<=C(1+n)^r              (AM.10)
```

for one fixed `r`.  Here is the local derivation.  On `[1/2,1]`,
`|xi_n'|<=2|D_u xi_n|`, so the last line of `(AM.9)` controls its `L1` norm.
On `[0,1/2]`, the factor `1-x^2` is bounded below and the middle line of
`(AM.9)` controls `xi_n''`; evenness gives `xi_n'(0)=0`.  One-dimensional
Sobolev then controls the supremum.

Since `xi_n` is supported in `[0,1]`, one integration by parts in its cosine
transform gives, for `y>=1`,

```text
|eta_n(y)|
 <=C(1+n)^r/y.                                        (AM.11)
```

Support of `P eta_n` now makes the coefficient in `(AM.7)`

```text
<xi_n,theta(rho^-1)zeta_n>
 =rho^(1/2)/sqrt(1-lambda_n^2)
   integral_(1/rho)^1 xi_n(x)eta_n(rho x)dx.          (AM.12)
```

Use `(AM.10)--(AM.11)`:

```text
|tau_n <xi_n,theta(rho^-1)zeta_n>|

 <=C (1+n)^(2r)|lambda_n|/(1-lambda_n^2)
   rho^(-1/2) integral_(1/rho)^1 dx/x

 =C (1+n)^(2r)|lambda_n|/(1-lambda_n^2)
   rho^(-1/2)log(rho).                                (AM.13)
```

Every fixed low-mode denominator is finite because `|lambda_n|<1`.  For all
large `n`, it is bounded away from zero, and `(AM.8)` sums against every fixed
polynomial.  Summing `(AM.13)` proves `(AM.1)`.

This is a tail bound for the source-owned static series itself.  No finite
section or prime-number estimate enters its proof.

## 5. Add the archimedean Weil coefficient

The static Sonin trace in `(AM.7)` is `W_infinity+epsilon`, not `epsilon`
alone.  CC20 source equation `bombieriexplicit2` gives the regular
archimedean density before half-density normalization.  After
`k(rho)=rho^(-1/2)f(rho)`, its positive-rho coefficient is, up to the fixed
sign and symmetric inverse orientation,

```text
rho^(1/2)/(rho-rho^(-1)).                             (AM.13a)
```

For `rho>=2`,

```text
rho^(1/2)/(rho-rho^(-1))
 =rho^(-1/2)/(1-rho^(-2))
 <=4/3 rho^(-1/2).                                    (AM.13b)
```

Combining `(AM.1)` and `(AM.13b)` proves that the complete static Sonin trace
coefficient has the bound

```text
O(rho^(-1/2)(1+log rho)).                             (AM.13c)
```

## 6. Why this does not close Proof 275

The two objects are different:

```text
epsilon(rho):
  coefficient in the static identity Tr(theta(f)S)-W_infinity(f);

q_R(z;g):
  Tr(W partial_a R_a|_(a=0))
  =a root-smoothed projection Dirichlet pairing.       (AM.14)
```

Proof 253 writes the latter as

```text
D_R(w,h)=Tr([M_w,R]*[M_h,R]),                         (AM.15)
```

not as the single static matrix coefficient in `(AM.7)`.  Expanding
`(AM.15)` before proving a same-object identity can lose the outer/Sonin/
prolate cancellation guarded by Proofs 258 and 273.

There is a second boundary.  The route applies the root differential

```text
Q=-(rho partial_rho)^2+1/4.                           (AM.16)
```

CC20 derives a series for `Q epsilon`, but its explicit uniform estimates in
Appendix `Issues of convergence` are stated for `1<=rho<=2`.  Applying two
derivatives to `(AM.1)` without retaining oscillation does not prove a
large-`rho` bound.  Do not infer one from the undifferentiated tail.

## 7. Source evidence

Primary source:

```text
Connes and Consani,
Weil positivity and Trace formula, the archimedean place,
arXiv:2006.13771v1.
https://arxiv.org/abs/2006.13771

Relevant source labels in weil-compo.tex:
sch18intro   explicit delta formula;
bombieriexplicit2 archimedean Weil coefficient;
sonine1     static Sonin trace identity;
sonine0     epsilon prolate expansion;
rapid-decay prolate eigenvalue bound;
Rokh        endpoint bound;
boundWang   polynomial Sobolev bound;
sonineQ     Q epsilon formula.
```

Burnol supplies the entire de Branges evaluator framework for the same Sonin
space, but does not state the semilocal moving-first-jet estimate:

```text
Burnol,
On the Sonine Spaces associated by de Branges to the Fourier Transform,
arXiv:math/0208121.
https://arxiv.org/abs/math/0208121
```

## 8. Reproduction

Run in WSL2:

```text
python3 -B docs/proofs/276_cc20_static_half_power_tail_probe.py

python3 -B docs/proofs/276_cc20_static_half_power_tail_probe.py \
  --maximum-log-shift 30 --maximum-index 240 --polynomial-degree 12
```

The certificate evaluates `(AM.3)`, checks inversion symmetry, and verifies
that the analytic bound in `(AM.8)` remains summable after a fixed polynomial
weight.  It does not numerically construct `epsilon` and it does not test the
missing identity in `(AM.14)`.

## 9. Route judgment

Proof 276 proves that the desired half-power is genuinely present in the
source's static Sonin correction.  It also prevents the next ownership error:
the static correction cannot be substituted for the moving projection first
jet merely because their exponents match.

Proof 277 identifies the exact remaining combination on the actual CC20
carrier:

```text
|Tr(T_(w h_z)^R-T_w^R T_(h_z)^R)|
 <=C(1+z)^(2d)exp(-z/2)norm(g)_(H^r)^2.              (AM.17)
```

The first raw static coefficient has the displacement tail proved here.  Its
route-smoothed polynomial support-width cost and the compressed Toeplitz
product are not controlled by that fact.  After `(AM.17)`, the result must
still be inserted into Proof 273's complete
determinant-resummed renewal.  Gate 3U, the finite-S sign, arithmetic
same-object trace identity, negative-owner integration, Burnol's identity,
and RH remain open.  No Lean owner or route rewire is authorized.
