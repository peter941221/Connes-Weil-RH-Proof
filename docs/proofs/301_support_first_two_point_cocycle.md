# Proof 301: Support-first two-point covariance cocycle

Date: 2026-07-16

Status: exact finite-dimensional reduction of the Sonin Toeplitz covariance to
a two-point finite-difference distribution, plus an exact synchronized-flow
readback.  A static complete-Euler-product cocycle is also verified, but is
explicitly rejected as a substitute for the moving projection owner.  Compact
root support therefore enters before any mode or prime split.  The construction
avoids a raw translated projection trace and keeps the signed outer-minus-Sonin
kernel.

This does not prove the source analytic strip estimate, Gate 3U, the finite-`S`
sign, the arithmetic same-object identity, negative-owner integration,
Burnol's all-zero identity, or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| projection Toeplitz covariance                 | exact two-point identity     |
| root multiplier / correlation reconstruction   | exact                        |
| compact support before mode expansion          | exact                        |
| nested E-R signed kernel                       | exact                        |
| static Euler product cocycle                   | exact, not route owner       |
| synchronized moving-kernel prime sum          | exact finite readback        |
| local Euler difference                         | explicit one-half-power      |
| static product -> moving endpoint substitution | rejected by exact guard      |
| primewise absolute-value estimate              | forbidden / unnecessary      |
| combined kernel analytic strip                 | open source theorem          |
| uniform moving-band bound                      | open                         |
| Gate 3U and RH                                 | unproved                     |
+------------------------------------------------+------------------------------+
```

The ownership move is

```text
Toeplitz covariance on the source carrier
  -> two-point projection-kernel difference
  -> compact root correlation pairing
  -> synchronized moving E/R kernel with full prime history
  -> one combined E/R/K_prol kernel estimate.             (BL.1)
```

The first four arrows are algebra.  The static product telescope below is a
separate guard; it is not silently identified with the moving owner.  Only the
final kernel estimate is analytic and remains unproved.

## 2. Projection covariance as a two-point difference

Let `J` be an orthogonal projection on a finite or continuous spectral carrier
and let `W=M_w`, `H=M_h` be diagonal multipliers.  The Toeplitz covariance is

```text
S_J(w,h)
 :=Tr(J W (I-J) H J).                                (BL.2)
```

For a finite matrix with kernel `J_(x,y)`, direct expansion and `J^2=J` give

```text
S_J(w,h)
 =sum_(x,y) w(x)(h(x)-h(y)) |J_(x,y)|^2

 =1/2 sum_(x,y)
      (w(x)-w(y))(h(x)-h(y)) |J_(x,y)|^2.             (BL.3)
```

The second line is valid for complex multipliers as an algebraic identity: the
measure `|J_(x,y)|^2` is symmetric in `x,y`.  In the continuous source, `(BL.3)`
is the definition of the completed distributional pairing after Proof 261's
root-sandwiched trace has made the scalar legal.  It is not a claim that every
individual translated projection is trace class.

This is the exact point where the two-point formulation improves the route:

```text
raw point object:     Tr(U_z(B_S-B))       forbidden;
completed object:     <two finite differences, |J(x,y)|^2>
                                             legal after root pairing. (BL.4)
```

The vanishing rules are immediate:

```text
S_J(1,h)=0,
S_J(w,1)=0,
```

and the two-point kernel has a zero whenever either finite difference is
constant.  These are the scalar versions of coherent bulk cancellation.

## 3. Compact root support enters first

Use the unitary finite Fourier convention on a discrete test carrier only to
display the exact algebra.  For a compact root `g`, put

```text
widehat g(k)=N^(-1/2) sum_n g(n) exp(-i theta_k n),
w(k)=|widehat g(k)|^2,
theta_k=2 pi k/N.                                    (BL.5)
```

Its circular correlation is

```text
F_g(u)=sum_n conjugate(g(n)) g(n+u),
```

and Fourier inversion gives

```text
w(k)=N^(-1) sum_u F_g(u) exp(-i u theta_k).            (BL.6)
```

If `supp(g)` is contained in `[-B,B]` and the carrier is large enough to avoid
wraparound, then

```text
supp(F_g) subset [-2B,2B].                            (BL.7)
```

For the exponential mode `h_z(k)=exp(i z theta_k)`, define the two-point mode
functional only through the completed covariance:

```text
A_J(u,z)
 :=1/2 sum_(x,y)
    (exp(-i u theta_x)-exp(-i u theta_y))
    (exp(i z theta_x)-exp(i z theta_y))
    |J_(x,y)|^2.                                      (BL.8)
```

Then `(BL.3)` and `(BL.6)` give the support-first identity

```text
S_J(w,h_z)
 =N^(-1) sum_(|u|<=2B) F_g(u) A_J(u,z).              (BL.9)
```

The continuous source statement is the distributional analogue

```text
Q_S(eta,xi)
 =<F_(eta,xi), A_(E,R,S)(.,z)>,

supp(F_(eta,xi)) subset [-2B_root,2B_root],            (BL.10)
```

where `A_(E,R,S)=A_(E,S)-A_(R,S)` is a signed kernel distribution.  Equation
`(BL.10)` is not a raw point trace: `A_(E,R,S)` is only tested against the
completed compact cross-correlation.

The correct order is therefore

```text
root factorization
  -> compact correlation support
  -> signed two-point pairing
  -> mode / prime disintegration.                       (BL.11)
```

Taking an absolute value over all `u` before the pairing destroys the
correlation cancellation.  Proof 301's certificate measures this loss but does
not use it as a continuous estimate.

## 4. The nested outer-minus-Sonin kernel

For the route's nested projections `R<=E`, the moving band response is the
signed difference

```text
S_(E,R)(w,h)
 :=S_E(w,h)-S_R(w,h).                                  (BL.12)
```

Its two-point kernel is

```text
|E_(x,y)|^2-|R_(x,y)|^2,                               (BL.13)
```

not a positive projection mass.  Inserting the CC20 identity

```text
R=E E_hat E-K_prol                                    (BL.14)
```

must be done inside `(BL.12)`.  The outer crossing, second-support crossing,
and prolate commutator are one signed kernel after this substitution.  No
individual branch norm is a valid replacement.

The exact finite identity checked by the probe is

```text
S_(E,R)(w,h_z)
 =N^(-1) sum_(|u|<=2B)
     F_g(u)[A_E(u,z)-A_R(u,z)].                       (BL.15)
```

This is the two-point counterpart of Proof 282's moving-band cancellation and
Proof 278's centered Burnol boundary Gram.

## 5. Static Euler product cocycle and ownership guard

Let the normalized local Euler factors on the spectral carrier be

```text
b_p(theta)
 =(1-a_p)/(1-a_p exp(i L_p theta)),
a_p=p^(-1/2), L_p=log(p),

t_S(theta)=product_(p in S) b_p(theta).              (BL.16)
```

For any ordered finite family `p_1,...,p_n`, the pointwise product difference
has the exact cocycle telescope

```text
t_S(x)-t_S(y)
 =sum_(r=1)^n
   [product_(q<r) b_q(x)]
   [b_(p_r)(x)-b_(p_r)(y)]
   [product_(q>r) b_q(y)].                            (BL.17)
```

Every term retains the complete past and future factors.  The identity is just
the telescoping of two products; it does not take a norm or assume a prime
independence law.

For the local factor, put `q=a_p` and `phi=L_p theta`.  Then

```text
b_p(x)-b_p(y)
 =q(1-q)
   [exp(i phi_x)-exp(i phi_y)]
   /[(1-q exp(i phi_x))(1-q exp(i phi_y))].            (BL.18)
```

The denominator obeys

```text
|1-q exp(i phi)| >=1-q,
|b_p(theta)|<=1,                                      (BL.19)
```

so the explicit local difference has one `p^(-1/2)` factor.  No second factor
appears from positivity or from bounding the other product legs.  The missing
gain must come from the signed two-point kernel in `(BL.15)`.

Substituting `(BL.17)` into the *static* covariance `(BL.15)` gives

```text
S_(E,R)(w,t_S)
 =sum_(r=1)^n Omega_(p_r),                            (BL.20)
```

where each `Omega_(p_r)` contains the full prefix, local difference, suffix,
and the same compactly supported `F_g`.  This is an exact scalar analogue of
Proof 289's complete-prime Markov telescope, but it is only a statement about
the multiplier difference `t_S(x)-t_S(y)`.

It is not yet the route owner.  In the actual synchronized flow, the
projection itself moves with `T_S(alpha)`.  Replacing its moving kernel by the
base kernel and inserting `t_S` into the second multiplier changes the scalar.
Proof 301's moving cohort measures this owner mismatch directly; its relative
gap is `0.8901` in the default cohort and `0.9068` in the alternate cohort.

The forbidden replacement is

```text
|sum_r Omega_(p_r)|
  ->sum_r |Omega_(p_r)|,                              (BL.21)
```

because the exact product telescope and the outer/Sonin cancellation both live
in the signed sum.  The telescope may be used only after a separate theorem
identifies the moving kernel with this static cocycle, and the current guard
shows that such an identification is false for the finite model used here.

## 6. Actual synchronized moving kernel

Let the normalized complete Euler transport on the finite spectral carrier be

```text
T_alpha(theta)
 =product_(p in S) (1-alpha a_p exp(i L_p theta)),
a_p=p^(-1/2),

X_alpha=T_alpha' T_alpha^(-1)
 =-sum_(p in S) a_p exp(i L_p theta)
       /(1-alpha a_p exp(i L_p theta)),
h_alpha=Re(X_alpha).                                  (BL.22)
```

For a source projection `J`, let `J_alpha` be the orthogonal projection onto
`T_alpha Ran(J)`.  Put `B_alpha=E_alpha-R_alpha`.  The moving projection
derivative and the completed covariance give

```text
Tr(W B_alpha')
 =2 Re[S_(E_alpha)(w,X_alpha)-S_(R_alpha)(w,X_alpha)]
 =2[S_(E_alpha)(w,h_alpha)-S_(R_alpha)(w,h_alpha)].   (BL.23)
```

The second equality uses that the imaginary diagonal part of `X_alpha`
commutes with the diagonal detector `W`; it is a finite identity and requires
the fixed-`S` trace legality in the continuous source.

Now apply the root correlation before splitting the generator.  Define

```text
A_(J,alpha)(u,h)
 :=1/2 sum_(x,y)
   (exp(-i u theta_x)-exp(-i u theta_y))
   (h(theta_x)-h(theta_y)) |J_alpha(x,y)|^2.          (BL.24)
```

Then the actual moving scalar is

```text
S_(E_alpha,R_alpha)(w,h_alpha)
 =N^(-1) sum_(|u|<=2B)
    F_g(u)[A_(E,alpha)(u,h_alpha)
          -A_(R,alpha)(u,h_alpha)].                  (BL.25)
```

Since `h_alpha=sum_p h_(p,alpha)`, linearity gives a prime sum, but every
prime term retains the complete moving kernels `E_alpha` and `R_alpha`:

```text
A_(E,alpha)(u,h_alpha)-A_(R,alpha)(u,h_alpha)
 =sum_(p in S)
   [A_(E,alpha)(u,h_(p,alpha))
    -A_(R,alpha)(u,h_(p,alpha))].                     (BL.26)
```

Integrating `(BL.23)` over `alpha` recovers Proof 282's exact endpoint
response.  This is the route-owned prime decomposition.  It differs from the
static telescope `(BL.17)` precisely by the transported projection kernel.

The synchronized finite certificate checks all three identities in `(BL.23)--
(BL.26)`, including an independent finite-difference derivative of the moving
projection.

## 7. New analytic contract

The exact algebra reduces the source problem to one combined distributional
estimate.  For a compact cross-correlation `F` and displacement `z`, the
target is

```text
|2 integral_0^1
    <F,A_(E,alpha,R,alpha)(.,h_alpha)> dalpha|
 <=C(1+B_root)^d
      norm(eta)_(H^r) norm(xi)_(H^r),                 (BL.27)
```

uniformly in finite `S`.  For an individual displacement mode
`h_(p,m,alpha)` the source input needed to close this bound has the
half-power form

```text
|integral_0^1
   <F,A_(E,alpha,R,alpha)(.,h_(p,m,alpha))> dalpha|
 <=C poly(m log p) p^(-m/2)
      norm(eta)_(H^r)norm(xi)_(H^r),                  (BL.28)
```

with the extra gain, if it exists, coming only after the signed complete sum.
The moving kernels, not the static product cocycle, are the owner of `(BL.27)`.

The proposed source proof is now specific:

```text
1. insert the CC20 E/E_hat/K_prol kernel into A_(E,alpha,R,alpha);
2. prove the outer and prolate boundary residues cancel in the combined kernel;
3. shift the combined displacement contour to the first Gamma/prolate strip;
4. apply (BL.7) before estimating the shifted pairing;
5. retain the full moving kernels in the generator sum (BL.26);
6. integrate the synchronized flow and take one absolute value last. (BL.29)
```

This is stronger than estimating CC20's static `epsilon` term: `(BL.27)` is a
two-point moving covariance.  It is also safer than a raw analytic-strip claim
for one branch, because branchwise strips can have nonzero boundary residues
which cancel only in `(BL.15)`.

## 8. Finite certificate

`301_support_first_two_point_cocycle_probe.py` checks:

```text
projection-kernel covariance identity (BL.3);
root multiplier reconstruction and support (BL.6)--(BL.7);
support-first pairing (BL.9) and nested signed pairing (BL.15);
static product telescope and its owner-mismatch guard (BL.17);
actual synchronized moving kernel and prime generator sum (BL.23)--(BL.26);
local resolvent difference (BL.18);
the absence of a pointwise contraction excess in (BL.19);
support and prime-channel cancellation guards.          (BL.24)
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/301_support_first_two_point_cocycle_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/301_support_first_two_point_cocycle_probe.py \
  --size 40 --support-radius 4 --outer-rank 16 --inner-rank 9 \
  --displacement 6.1 --seed 2301 \
  --primes 2,3,5,7,11,13,17,19 --flow-time 0.71
```

The two cohorts report:

```text
+--------------------------------------------+-------------+-------------+
| diagnostic                                 | default     | alternate   |
+--------------------------------------------+-------------+-------------+
| maximum exact error                        | 6.07e-16    | 5.83e-16    |
| support-mode cancellation ratio            | 6.286       | 1.880       |
| outer-inner cancellation ratio             | 9.568       | 6.931       |
| prime-channel cancellation ratio           | 1.220       | 2.146       |
| moving support-first pairing error         | 3.54e-17    | 2.86e-17    |
| moving prime-generator sum error           | 4.86e-17    | 4.51e-17    |
| moving endpoint integration error          | 2.08e-17    | 8.68e-17    |
| static product owner gap                   | 0.890       | 0.907       |
| local amplitude exponent                   | 1.0121      | 1.0105      |
| a^(-2)-scaled local response               | 1148.6      | 1326.4      |
+--------------------------------------------+-------------+-------------+
```

The ratios are finite ownership guards, not estimates.  They show why taking
absolute values before support-first recombination is materially weaker.  The
local exponent is one, so the missing extra half-power is not hidden in the
local Euler resolvent.

## 9. Route judgment

Proof 301 closes a useful algebraic gap between the compact-root endpoint and
the actual synchronized moving owner:

```text
compact support is applied to a legal scalar pairing;
the nested E/R kernel remains signed;
each prime generator retains the complete moving E/R kernel;
raw translated projection traces are never introduced.               (BL.30)
```

The static product telescope `(BL.17)` is deliberately marked as a guard, not
as the route endpoint: the finite owner-mismatch gap is close to one in both
cohorts.  Proof 301 did not claim the combined moving kernel had the required
analytic strip; Proof 302 now rejects the unpaired global contour version of
that idea.  The source documents remain the boundary of what is imported:

```text
CC20 static Sonin/prolate trace:
  https://arxiv.org/abs/2006.13771

CCM24 semilocal Sonin transport:
  https://arxiv.org/abs/2310.18423

Burnol Sonine/de Branges boundary formula:
  https://arxiv.org/abs/math/0208121
```

None of those sources states `(BL.27)`.  The active successor is Proof 302's
source divided-difference bridge, not a bare global strip claim.  No Lean owner or route consumer is
changed by Proof 301.  Gate 3U, the finite-`S` sign, arithmetic same-object
identity, negative-owner integration, Burnol's all-zero identity, and RH
remain open.

## 10. Successor: Proof 302

Proof 302 rejects the unpaired global contour target.  CC20's `Qdelta` splits
as `-2 Dirac_0` plus an oscillatory regular tail, while Appendix D/E supplies
the source divided-difference kernel

```text
([H,f])(s,t)=i/pi * (f(s)-f(t))/(s-t).
```

The next route is therefore

```text
isolate the diagonal residue
  -> use quantized divided differences for completed crossings
  -> recombine E/R/K_prol
  -> prove the compact root-paired moving estimate
  -> Gate 3U.                                             (BL.31)
```

See `docs/proofs/302_quantized_divided_difference_residue_guard.md`.
