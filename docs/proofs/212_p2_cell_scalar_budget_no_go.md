# Proof 212: the p=2 cell channel exceeds the scalar-two budget

Date: 2026-07-13

Status: the raw translation-operator calculation and `R_8>2` certificate are
accepted.  Its original same-object route interpretation is superseded by
Proof 217: in the CC20 Q-root identity the prime operator acts on
`g=(d/dx+1/2)xi`, while `2 Id+compact` acts on `xi`.  The calculation remains a
valid warning that scalar-only domination is impossible, but it is not by
itself the correctly owned M4 relative form.  RH remains unproved.

## 1. Exact finite-prime operator

The project has the same-object whole-line owner

```text
K_(p,m)
  = log(p)/sqrt(p^m) * (T_(m log p)+T_(-m log p)).       (S.1)
```

Its quadratic form on the selected convolution root is the finite-prime atom.
This is proved in
`ConnesWeilRH/Source/CCM25Concrete/SelectedPrimeTranslationQuadratic.lean`:

```text
primePowerTranslationOperator                         lines 72-80
inner_primePowerTranslationOperator_eq_finitePrimeTerm_pow
                                                       lines 105-139
```

No trace or asymptotic normalization is used below; (S.1) is analyzed directly
on its genuine whole-line carrier.

## 2. Exact cell reduction

Put

```text
L=log(2),
c=2^8=256,
I=[0,8L).
```

Partition `I` into the eight half-open cells

```text
I_j=[jL,(j+1)L),  0<=j<8.
```

For any nonzero `psi` in `L2(0,L)`, define the repeated-cell vector

```text
xi(jL+t)=psi(t),  0<t<L.                               (S.2)
```

The visible powers `2^m<c` are `m=1,...,7`.  Zero extension outside `I` gives

```text
<xi,T_(mL)xi>=(8-m)||psi||_2^2,
<xi,T_(-mL)xi>=(8-m)||psi||_2^2.                       (S.3)
```

Since `||xi||_2^2=8||psi||_2^2`, the `p=2` finite-prime operator has Rayleigh
quotient

```text
R_8
 = (2/8) sum_(m=1)^7 (8-m) L 2^(-m/2)
 = (L/4) sum_(m=1)^7 (8-m)2^(-m/2).                    (S.4)
```

This is the constant-vector Rayleigh quotient of the exact `8 x 8` Toeplitz
matrix whose distance-`m` entries are `L 2^(-m/2)`.

## 3. Elementary strict certificate

Use

```text
1/sqrt(2) > 707/1000,                                  (S.5)
log(2) > 693/1000.                                     (S.6)
```

Equation (S.5) follows by squaring, since
`707^2/1000^2=499849/1000000<1/2`.

For (S.6), the positive atanh series gives

```text
log(2)
 = 2 sum_(k>=0) 1/((2k+1)3^(2k+1))
 > 2 sum_(k=0)^3 1/((2k+1)3^(2k+1))
 = 53056/76545
 > 693/1000.                                           (S.7)
```

Substituting (S.5)-(S.6) into (S.4) and doing exact rational arithmetic gives

```text
R_8
 > (693/4000) sum_(m=1)^7 (8-m)(707/1000)^m
 > 2.                                                  (S.8)
```

The exact rational margin in (S.8) is positive.  The actual value is

```text
R_8 = 2.007741159155714...                              (S.9)
```

The strict proof uses (S.5)-(S.8), not the decimal in (S.9).

## 4. The route vanishings do not remove the cell channel

In additive log coordinates, each Mellin evaluation imposed on the root has
the form

```text
Lambda_k(xi)=integral_I exp(s_k x) xi(x) dx             (S.10)
```

for one of the finitely many route points `s_k` (in particular the zero and
pole rows).  Substituting (S.2) turns (S.10) into

```text
Lambda_k(xi)=integral_0^L W_k(t) psi(t) dt              (S.11)
```

with one explicit `W_k` in `L2(0,L)`.  The orthogonal complement of finitely
many `W_k` is infinite-dimensional and contains nonzero smooth compactly
supported functions.  Hence `psi` may be chosen so that all three route
evaluations vanish while (S.3)-(S.9) remain unchanged.

More strongly, choose an orthonormal sequence `psi_n` in that finite-codimension
subspace and let `xi_n` be its repeated-cell lifts.  Then `xi_n` is weakly zero
and

```text
<xi_n,K_2 xi_n>/||xi_n||^2 = R_8 > 2                   (S.12)
```

for every `n`.

## 5. Compact corrections cannot repair the deficit

For every compact operator `C` on the root `L2` space,

```text
<xi_n,C xi_n>/||xi_n||^2 -> 0.                          (S.13)
```

Combining (S.12)-(S.13),

```text
lim_n <xi_n,(2 Id-K_2+C)xi_n>/||xi_n||^2
  = 2-R_8
  < 0.                                                  (S.14)
```

Thus the scalar `+2 Id` obtained from the opposite of the CC20
`-2 Id+compact` remainder cannot by itself pay for the exact `p=2` channel.
Adding the other prime channels may create test-dependent cancellations, but
no per-prime or scalar-only domination may discard the archimedean positive
trace and still claim a uniform sign theorem.

## 6. What remains alive

The corrected archimedean identity has the structural shape

```text
QW_S(root)
  = PositiveTrace_infinity(Q root)
      + 2||root||^2
      - Compact_infinity(root)
      - FinitePrimeTranslationSum(root).                (S.15)
```

Proof 212 shows that the first term in (S.15) is essential.  A viable
common-domain route must prove, on the same repeated-cell fibers and then on
the full form domain, a quantitative estimate of the shape

```text
PositiveTrace_infinity(Q root)
  >= <root,(FinitePrimeTranslationSum-2 Id
             +Compact_infinity)root>.                   (S.16)
```

It is not enough to cite `PositiveTrace_infinity>=0`.  Equation (S.16) is the
smallest remaining archimedean/Euler relative-form gate.  It must be obtained
from the genuine CC20 multiplier/Sonin owner, not stored as a Weil-sign field.

## 7. Reproduction

The exact-rational certificate uses only the Python standard library:

```text
python3 -B docs/proofs/212_p2_cell_scalar_budget_probe.py
```

Expected key lines:

```text
rayleigh_float=2.007741159155714
rayleigh_float_margin=0.007741159155714
```

## 8. Route judgment

```text
p=2 cell reduction:                       exact
R_8>2:                                    exact rational certificate
three route vanishings:                   finite codimension; no norm reduction
2 Id plus compact domination:             rejected at c=256
archimedean positive trace as mere >=0:   insufficient
archimedean-coupled relative form:         still alive
next hard gate:                            quantitative inequality (S.16)
Lean owner:                                none
RH:                                        unproved
```
