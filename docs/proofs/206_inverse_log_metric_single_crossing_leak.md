# Proof 206: Inverse-log metric single-crossing leak

Date: 2026-07-13

## Result

The inverse-log metric proposed in proof 205 is positive, but it is not an
exact finite-prime trace owner. Its purported interrupted remainder already
contains another noncompact one-step prime crossing at second order.

```text
positive metric:                         retained
claimed intrinsic Euler-log channel:     false
two-boundary remainder:                  false
weighted Wiener summation gate:          never reached
Plan 046:                                rejected
```

The failure is algebraic. The scalar `b_S` that repairs positivity disappears
from `Q H_S^(-1) R`, but it does not disappear through the compressed inverse
`(R H_S R)^(-1)`.

## Route obligation

```text
route obligation:
  decide whether the positive inverse-log metric has exactly the selected
  Euler-log crossing modulo a trace-norm summable two-boundary ideal

old weak path:
  call Q(I-H_S^(-1))R the direct channel and classify every term with an
  internal Q as an additional boundary crossing

new mathematical owner:
  none; the proposed owner is rejected below

consumer to rewire:
  Plan 032 Gate 3 and Plan 046

forbidden circular inputs:
  a stored finite-S trace identity, a declaration that internal Q implies
  compactness, or a weighted Wiener theorem applied before principal-symbol
  cancellation

smallest verification target:
  one prime, one half-line, and the coefficient from e_0 to e_(-1)

focused axiom audit:
  not applicable; no Lean declaration is introduced
```

## Exact block inverse

Write `Q=I-R`, let

```text
K=H^(-1)=c I-ell,
c=1+b,
A=R H R | Ran(R),
X=Q H R A^(-1).
```

Use blocks relative to `Ran(R) direct-sum Ran(Q)`. The `Q,R` block of
`K H=I` is

```text
K_QR H_RR + K_QQ H_QR=0.
```

Since `K>=I`, its `Q,Q` compression is invertible. Multiplication on the right
by `H_RR^(-1)` gives the exact formula

```text
X
  =-K_QQ^(-1) K_QR
  =(c Q-Q ell Q)^(-1) Q ell R.                         (B.1)
```

Proof 205 selected

```text
D=Q ell R                                               (B.2)
```

as the Euler-log channel. Equations (B.1)--(B.2) show that the actual
difference is

```text
E=X-D
 =((c Q-Q ell Q)^(-1)-Q) Q ell R.                      (B.3)
```

An internal `Q` in (B.3) is only a compression. It need not be flanked by two
nontrivial off-diagonal translation blocks, so it is not by itself a second
Hilbert--Schmidt boundary crossing.

There is also a normalization invariant that the proposed split fails. For
every scalar `lambda>0`, replacing `H` by `lambda H` leaves both the range
`H^(1/2) Ran(R)` and the graph map unchanged:

```text
Q (lambda H) R(R(lambda H)R)^(-1)=X.
```

But the no-internal-`Q` prescription becomes

```text
Q(I-(lambda H)^(-1))R
  =-lambda^(-1) Q H^(-1)R.
```

Thus the alleged direct term changes while the positive projection and its
trace do not. It cannot be an intrinsic arithmetic channel of that owner.

## One-prime second-order calculation

Let `U` be the unit translation by `log(p)` and put

```text
a=p^(-1/2),
T=U+U^*,
T_2=U^2+U*^2.
```

For one prime,

```text
ell(a)=-a T-(a^2/2)T_2+O(a^3),
b(a)=2a-a^2+O(a^3).
```

Therefore

```text
K(a)
 =I+a(2I+T)+a^2(-I+T_2/2)+O(a^3),

H(a)
 =I-a(2I+T)+a^2(7I+4T+T_2/2)+O(a^3).                 (B.4)
```

Expanding the actual compressed inverse in (B.1), or directly expanding
`Q H R(R H R)^(-1)`, gives

```text
X(a)
 =-a Q T R
  +a^2(2 Q T R-(1/2)Q T_2 R+Q T Q T R)
  +O(a^3).                                             (B.5)
```

The selected Euler-log term is

```text
D(a)=-a Q T R-(a^2/2)Q T_2 R+O(a^3).                  (B.6)
```

Subtracting (B.6) from (B.5) proves

```text
E(a)=a^2(2 Q T R+Q T Q T R)+O(a^3).                   (B.7)
```

The word `Q T Q T R` has even total translation degree. It cannot cancel the
odd one-step block `2 Q T R`. This is precisely the channel that proof 205
claimed was absent.

## Noncompact fiber witness

Decompose the additive line into translation fibers of width `L=log(p)`:

```text
L2(R)
  = L2([0,L)) tensor ell2(Z),

U_L = I tensor bilateralShift,
R   = I tensor projection_(n>=0).
```

Compress (B.7) between the fiber coordinates `e_0` and `e_(-1)`. The even
word has zero matrix element there, while the one-step word gives

```text
<e_(-1),E(a)e_0>=2a^2+O(a^3).                          (B.8)
```

For every sufficiently small positive `a`, (B.8) is nonzero. Since primes are
unbounded, this applies to actual parameters `a=p^(-1/2)`. On the continuous
line the compressed block is a nonzero scalar multiple of the identity on
`L2([0,L))`, hence has infinite multiplicity and is not compact.

The finite-section WSL probe in
`206_inverse_log_metric_single_crossing_probe.py` is only a sanity check. It
agrees with the proved limit:

```text
+----------------+----------------+
| a              | E[-1,0] / a^2 |
+----------------+----------------+
| 0.030000000000 | 1.848701080    |
| 0.050000000000 | 1.760990383    |
| 0.080000000000 | 1.645215735    |
| 1/sqrt(101)    | 1.578442728    |
| 1/sqrt(2)      | 0.734439480    |
+----------------+----------------+
```

The proof uses the nonzero asymptotic coefficient `2`, not the numerical
value at `p=2`.

## Why Wiener summability cannot repair it

A weighted Wiener lemma can prove exponential or polynomially weighted
summability of Fourier coefficients of `(cI-ell)^(-1)`. It cannot change the
operator-ideal class of the coefficient already isolated in (B.8).

```text
coefficient summability
  controls the sum of legal residual words;

nonzero I tensor |e_(-1)><e_0|
  is an illegal one-crossing principal block before that sum.
```

Applying the Wiener theorem first would merely sum the wrong decomposition.

## Verdict

```text
positivity repair by b_S:                 correct
Q I R scalar cancellation:                correct but insufficient
compressed-inverse scalar cancellation:   false
exact all-prime-power owner:               rejected
two-boundary interrupted remainder:        rejected
Plan 046:                                  rejected
Lean owner:                                forbidden
RH:                                        unproved
```

See proof 205 for the proposed construction and proof 042 for the earlier
endpoint-metric coefficient failure.
