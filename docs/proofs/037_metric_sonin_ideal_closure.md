# Metric Sonin Ideal Closure

Date: 2026-07-12

Status: superseded by `040_metric_sonin_domain_rejection.md`. The ideal-class
argument below does not construct the fixed-`S` post-`Q` operator on CC20's
test-root Hilbert space. In particular, the positive trace-class correction in
the angle decomposition of `P P_hat P` is not CC20's post-`Q` compact integral
operator. The finite-`S` compact remainder therefore remains unproved. RH
remains unproved.

## 1. Source Trace-Class Decomposition

CC20 gives the exact spectral decomposition

```text
P P_hat P
  = R_Sonin + K_prol,

K_prol=sum_n lambda_n^2 |zeta_n><zeta_n|.                (I.1)
```

Source: `weil-compo.tex:1072-1076`, equation `spectral`.

The eigenvalue sum is finite; CC20 records

```text
sum_n lambda_n^2
  = 2(Si(4pi)/(4pi)+1)
  approximately 2.237484835.                             (I.2)
```

Source: `weil-compo.tex:1100-1103`.

Thus `K_prol` is positive trace class. Any expanded metric word containing
`K_prol` is trace class after multiplication by bounded Euler and compressed
metric factors.

## 2. Smoothed Boundary Crossings

CC20 proves that the quantized differential of a Schwartz multiplier is an
infinitesimal of infinite order, hence trace class:

```text
[H,f] is trace class for every Schwartz f.                (I.3)
```

Source: `weil-compo.tex:2105-2120`, Lemma `quantsmooth`.

In the additive log coordinate, a finite Euler power `U_p^m` is translation by
`m log(p)`. If `C_h` is convolution by a Schwartz kernel `h`, the one-boundary
block satisfies the exact Hilbert--Schmidt estimate

```text
norm(C_h [P,U_p^m])_HS^2
  = |m| log(p) norm(h)_2^2.                              (I.4)
```

This is the kernel calculation already recorded in plan 026. Derivative and
Sobolev factorization strengthen the smoothed block to trace class with at
most polynomial growth in `|m|`.

The Fourier-conjugate cutoff has the same estimate. Therefore:

```text
one boundary crossing
  -> the single-crossing arithmetic channel plus a trace-legal boundary term;

two or more boundary crossings
  -> product of two Hilbert--Schmidt factors, hence trace class;

one K_prol insertion
  -> trace class by (I.1)--(I.2).                         (I.5)
```

## 3. Euler Summability After Q

The logarithmic metric flow has coefficients `p^(-m/2)/m`. Applying the
support-preserving differential `Q` contributes at most a polynomial factor in
`m log(p)`. For every fixed prime and every integer `d`,

```text
sum_(m>=1) p^(-m/2) m^d < infinity.                      (I.6)
```

Consequently the trace-norm series of all smoothed multi-crossing and prolate
correction words converges after `Q`.

## 4. Relative Compactness Conclusion

Assume the fixed-S trace identity is organized so that every single-crossing
`Q U_p^m R` channel is read as its corresponding finite-prime Weil atom. Then
the remaining post-`Q` quadratic operator has the form

```text
Remainder_(S,I,Q)
  = -2 Id + K_(S,I),

K_(S,I) compact and self-adjoint.                         (I.7)
```

The scalar `-2 Id` is the archimedean essential part proved by CC20. Plans
035--036 remove the raw finite-prime scalar identity and put every other Euler
word into the trace-class classes (I.5)--(I.6). Thus finite Euler factors do
not change the essential spectrum in (I.7).

The local single-crossing trace read-off is proved in
`docs/proofs/038_single_crossing_weil_read_off.md`: a crossing of length
`m log(p)` gives exactly the same convolution-square evaluation multiplied by
`p^(-m/2)log(p)`. The minus sign in the metric projection agrees with the
`-sum_p W_p` leg of CCM25 `QW`. Equation (I.7) still requires the global CC20
angle decomposition to identify the two cutoff orientations. It does not prove
the norm or sign of `K_(S,I)`.

## 5. Former Sign Gate

The original analysis proposed two closures:

```text
strong closure:
  prove norm(K_(S,I))<2 on the route support/vanishing space;

conditioned closure:
  prove the spectral subspace of K_(S,I) for eigenvalues >=2 is finite
  and is annihilated by the existing route conditions.                  (I.8)
```

Compactness alone gives finiteness of the `>=2` spectral subspace, but it does
not show that triple Mellin vanishing annihilates it. Introducing arbitrary
bad-vector orthogonality would reopen the restricted-test RH-exit problem.

This spectral test is not authorized. No exact fixed-`S` post-`Q` operator on
the test-root Hilbert space was constructed, so a numerical section would
approximate a proxy rather than the route remainder.

CCM24's common de Branges realization proves stability of the Sonin function
space, not an identification with the test-root Hilbert space. The corrected
contract is recorded in `docs/proofs/040_metric_sonin_domain_rejection.md`.

The later same-object expansion gives a stronger obstruction: the endpoint
metric projection has twice the required `p^2` coefficient, leaving an excess
single crossing outside the compact ideal. See
`docs/proofs/042_metric_sonin_second_prime_power_rejection.md`.

## 6. Verdict

```text
prolate angle correction K_prol: positive trace class, source-proved.
smoothed one-crossing blocks: trace legal.
multi-crossing blocks: trace class.
Euler series after Q: trace-norm summable.
global fixed-S post-Q identity: unproved.
finite-Euler residual kernel: unconstructed.
compactness of that residual: unproved.
former de Branges norm gate: ill-typed.
RH: unproved.
```
