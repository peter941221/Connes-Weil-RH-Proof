# Proof 250: Chirp-Mixture Tail Gain and Central Obstruction

Date: 2026-07-15

Status: the dangerous negative-tail interiors in Proof 229 admit an exact
operator-valued chirp decomposition.  Every cell `n >= 1` gains the missing
Fourier half-power and has operator norm

```text
poly(log(p)) p^(-n).
```

This does not close Proof 249's quantitative finite-`S` gate.  The central
cell `n=0` has only the scale `p^(-1/2) log(p)` under the same decomposition,
and stable Nyström refinements show that this is an actual operator-scale
effect rather than only a loose majorant.  Therefore a termwise chirp estimate
cannot prove `p^(-m)` for the complete remainder.  The only surviving version
of the detector-specific route must first prove an exact signed cancellation
or extract a sign-controllable common central operator from the complete
nested crossing.  No such theorem is proved here.  RH remains unproved.

## 1. Exact negative-cell factorization

Fix one prime and put

```text
L=log(p),
a=p^(-1/2),
w_p(t)=[L-(1-a)t]/(1-a)^2,  0<=t<=L.                 (M.1)
```

Proof 229 gives, on the negative cell `x=-nL-t`,

```text
W_p(nL+t)=a^(n+1) w_p(t),

k_infinity(-nL-t)
 =2a^n exp(-t/2) cos(2pi p^(-n)exp(-t)),

k_infinity(r+nL+t)
 =2a^(-n) exp((r+t)/2) cos(2pi p^n exp(r+t)).         (M.2)
```

Multiplying all three expressions before taking absolute values cancels both
the `a^n` pair and the `t` half-density exactly:

```text
4a^(n+1) exp(r/2) w_p(t)
  cos(2pi p^(-n)exp(-t))
  cos(2pi p^n exp(r+t)).                              (M.3)
```

After splitting the fast cosine into its two complex phases, one orientation
has amplitude

```text
A_(p,n)(r,t)=exp(r/2)b_(p,n)(t),

b_(p,n)(t)
 =2a^(n+1)w_p(t)cos(2pi p^(-n)exp(-t)).               (M.4)
```

This is the missing exact structure behind Proof 229's qualitative bound
`(P.15)`: the amplitude is separable.  It is not a general two-variable FIO
amplitude.

## 2. The post-Q derivative preserves separability

Let

```text
D=partial_r-partial_t.
```

For every twice differentiable scalar function `b`,

```text
D^2[exp(r/2)b(t)]
 =exp(r/2)(partial_t-1/2)^2 b(t).                     (M.5)
```

Write

```text
c_n(t)=cos(2pi p^(-n)exp(-t)).
```

Then

```text
c_n'(t)
 =2pi p^(-n)exp(-t) sin(2pi p^(-n)exp(-t)),

c_n''(t)
 =-2pi p^(-n)exp(-t) sin(2pi p^(-n)exp(-t))
  -4pi^2 p^(-2n)exp(-2t) cos(2pi p^(-n)exp(-t)).      (M.6)
```

Consequently one complex interior after the two derivative transfers is

```text
T_(p,n)^sigma
 =integral_0^L d_(p,n)(t) K_(p^n exp(t))^sigma dt,    (M.7)

d_(p,n)(t)
 =2a^(n+1) {
     w_p(t)[c_n''(t)-c_n'(t)+c_n(t)/4]
     +w_p'(t)[2c_n'(t)-c_n(t)]
   },                                                  (M.8)
```

where `K_lambda^sigma` is exactly Proof 228's logarithmic chirp on the chosen
root interval:

```text
K_lambda^sigma(x,y)
 =exp((x-y)/2)exp(sigma 2pi i lambda exp(x-y)).        (M.9)
```

No transverse amplitude derivative is missing in `(M.7)`.

## 3. Bochner-Plancherel gain

Proof 228 proves, uniformly for every bounded root interval,

```text
norm(K_lambda^sigma)<=lambda^(-1/2).                  (M.10)
```

The Bochner integral triangle inequality therefore gives

```text
norm(T_(p,n)^sigma)
 <=p^(-n/2)
   integral_0^L |d_(p,n)(t)|exp(-t/2)dt.              (M.11)
```

For `n>=1`, and in fact also as an upper bound for `n=0`, equations
`(M.1)` and `(M.6)` give

```text
|d_(p,n)(t)|
 <=C (1+L) p^(-(n+1)/2),                              (M.12)
```

with one absolute constant for all `p>=2`.  Since

```text
integral_0^L exp(-t/2)dt=2(1-p^(-1/2))<=2,            (M.13)
```

one obtains

```text
norm(T_(p,n)^sigma)
 <=C (1+log(p)) p^(-n-1/2)
 <=C (1+log(p)) p^(-n),  n>=1.                        (M.14)
```

The conjugate phase has the same bound.  Thus every genuinely positive
negative-tail cell gains the missing Fourier half-power without a generic
`TT*` theorem.

## 4. Why the central cell is different

For `n=0`, equation `(M.11)` contains no frequency factor from `p^n`.
On every fixed `t` interval,

```text
d_(p,0)(t)
 =p^(-1/2) log(p) d_infinity(t)+O(p^(-1/2)),          (M.15)
```

where

```text
d_infinity(t)
 =2(partial_t-1/2)^2 cos(2pi exp(-t)).                (M.16)
```

Moreover, after division by `p^(-1/2)log(p)`, the operator in `(M.7)`
converges in the same Bochner atomic norm to

```text
T_infinity
 =integral_0^infinity
    d_infinity(t) K_(exp(t)) dt.                      (M.17)
```

The integral is norm convergent because `(M.10)` contributes `exp(-t/2)`.
The limit is not forced to be zero.  Its transformed kernel is the
one-sided Fourier integral

```text
integral_1^infinity
  [d_infinity(log(q))/q] exp(2pi i q u w)dq.           (M.18)
```

The coefficient at `q=1` is nonzero:

```text
d_infinity(0)=1/2-8pi^2 !=0.                          (M.19)
```

Thus the one-sided Fourier transform in `(M.18)` is not the zero
distribution.  On a root interval where its restriction is nonzero,
`T_infinity` is a nonzero operator.  The central interior therefore has the
natural scale

```text
norm(T_(p,0)) asymp p^(-1/2)log(p),                   (M.20)
```

not `p^(-1)`.

There is independent source-side evidence for the same obstruction.  Proof
225's twice-integrated formula leaves the fixed-center term

```text
k_infinity(0),                                        (M.21)
```

for every Euler width, while Proof 228 records that this term retains the
coefficient `a^m`.  Summing over `m` for one prime starts at
`a=p^(-1/2)`, not `a^2`.

This does not by itself prove that the complete signed nested crossing has a
nonzero central term.  Proof 227 forbids estimating separated phase and
orthogonalization pieces before their exact subtraction.  It does prove that
the termwise chirp-mixture method cannot establish Proof 249's complete
`p^(-m)` claim.  Any cancellation must now be displayed as an equality for
the full `Y_alpha+Y_alpha*`, not inferred from bounded dressings.

## 5. Dressing audit

For the cells `n>=1`, Proofs 230--234 preserve `(M.14)`:

```text
Euler translations and scattering commute with Q;
half-line cutoffs are contractions;
each no-prolate word creates only O((1+k)^2) cells and boundaries;
the word coefficient is bounded by eta^k;
eta<=2sqrt(2)/3<1.                                    (M.22)
```

Hence the tail-cell atomic bounds sum against

```text
sum_(k>=0)(1+k)^d eta^k<infinity.                     (M.23)
```

There is no hidden exponential dependence on the detector support in this
tail ledger.

The same closure does not improve the central cell.  Left and right
multiplication by contractions preserve an `O(p^(-1/2)log(p))` upper bound;
they do not turn it into `O(p^(-1))`.  Prolate insertions are trace class and
rapidly summable in their spectral index, but the current proofs give no
uniform `p^(-1/2)` translation-rate gain for their central contribution.

The full quantitative dressing theorem is therefore reduced to two precise
questions:

```text
1. Does the signed central component cancel in Y_alpha+Y_alpha*?
2. If not, can it be extracted as one common operator with a usable sign on
   the selected detector?                              (M.24)
```

Qualitative compactness does not answer either question.

## 6. Sparse support does not rescue absolute p^(-1/2)

Let the resonant centered pair from Proof 249 use translations `+-ell` and
normalizer `2cosh(ell delta)`, where `0<|delta|<1/2`.  After `N` convolution
copies, the translation coefficients are binomial.  In the convolution
square, the two-sided exponential moment corresponding to a
`p^(-1/2)` prime density is exactly

```text
[1/(2cosh(ell delta))^(2N)]
  sum_(j=-N)^N binom(2N,N+j) exp(j ell)

 =[cosh(ell/2)/cosh(ell delta)]^(2N).                 (M.25)
```

Since `|delta|<1/2`, the ratio in `(M.25)` is strictly greater than one.
Therefore the discrete cluster structure of the resonant support cannot make
an absolute `p^(-1/2)` sum contract.  This is the exact binomial form of the
Paley--Wiener rate obstruction already identified qualitatively in Proof 249.

## 7. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/250_chirp_mixture_interior_gain_probe.py

python3 -B docs/proofs/250_chirp_mixture_interior_gain_probe.py \
  --interval-bound 0.4 \
  --nystrom-cases 2:1,2:2,2:3 \
  --grid-sizes 320,384 \
  --quadrature-order 256

python3 -B docs/proofs/250_chirp_mixture_interior_gain_probe.py \
  --nystrom-cases 47:0,101:0,211:0 \
  --grid-sizes 256,384 \
  --quadrature-order 768 \
  --interval-bound 0.05 \
  --max-phase-step 0.9 \
  --primes 2,3,5 \
  --cells 6
```

The default tail run reports:

```text
cell_product_identity_error       4.158e-10
transferred_D2_relative_error     2.600e-07
max scaled quadrature bound       1.3184e+01
largest Nyström / analytic ratio  2.5070e-01
```

The central run reports, at its finest grid,

```text
+-----+----------------+---------------------------------+
| p   | operator norm  | norm * sqrt(p) / log(p)         |
+-----+----------------+---------------------------------+
|  47 | 0.8595543787   | 1.5305407844                    |
| 101 | 0.6354472932   | 1.3837485364                    |
| 211 | 0.4786767330   | 1.2992087991                    |
+-----+----------------+---------------------------------+
```

Both grid refinements agree in the displayed operator norms.  These numerical
values are diagnostics for `(M.20)`; the exact tail theorem is
`(M.1)--(M.14)`.

Primary source context:

```text
Connes--Consani, Weil Positivity and Trace Formula, the Archimedean Place
https://arxiv.org/abs/2006.13771

Connes--Consani--Moscovici, Zeta Zeros and Prolate Wave Operators
https://arxiv.org/abs/2310.18423
```

The latter proves semilocal Sonin transport and explicitly presents
semilocal Weil positivity as a program.  It does not provide the central
cancellation required by `(M.24)`.

## 8. Route judgment

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| exact separable negative-cell amplitude        | proved                   |
| D^2 preservation of separability               | proved                   |
| n>=1 Bochner-Plancherel p^(-n) gain            | proved                   |
| tail closure under no-prolate word dressings   | proved at profile level  |
| n=0 termwise p^(-1) gain                       | rejected                 |
| sparse-support rescue of absolute p^(-1/2)     | rejected by (M.25)       |
| signed complete central cancellation           | open, decisive           |
| quantitative prolate translation rate          | open                     |
| Proof 249 absolute remainder-smallness route   | not established          |
| same-object finite-S trace identity             | open                     |
| RH                                              | unproved                 |
+------------------------------------------------+--------------------------+
```

The next valid target is not a generic FIO theorem.  It is the exact central
coefficient of the complete signed crossing `(F.12)--(F.13)`.  A successor
must prove one of the following before returning to detector smallness:

```text
central coefficient = 0;

or

complete remainder
 = nonnegative scalar * common central operator
   +poly(log(p))O(p^(-1)) tail,
```

with a proved favorable sign of the common operator on one same-object
negative Yoshida detector.  If neither statement holds, Proof 249's current
detector-specific route is rejected.
