# Proof 205: Inverse-log metric projection candidate

Date: 2026-07-13

## Result

This proposed translation-invariant metric is positive, but proof 206 rejects
it as an exact finite-prime owner. The original calculation correctly isolates
one formal no-internal-`Q` subseries; it incorrectly assumes that every term
outside that subseries has two genuine boundary crossings.

```text
positivity:                    pass
formal selected coefficients:  a^m/m
intrinsic direct channel:       fail
two-boundary remainder:         fail
```

For a finite set `S_f` of primes, put

```text
a_p = p^(-1/2),
ell_p = log((I-a_p U_p)^*(I-a_p U_p)),
ell_S = sum_(p in S_f) ell_p,
b_S = sum_(p in S_f) 2 log(1+a_p),
H_S = ((1+b_S)I-ell_S)^(-1).                            (L.1)
```

Then `H_S` is positive and boundedly invertible, so the orthogonal projection
onto `H_S^(1/2) Ran(R)` is genuine and positive. The calculation below
formally selects

```text
Q ell_S R
  = -sum_(p in S_f) sum_(m>=1)
      a_p^m/m * Q(U_p^m+U_p^(-m))R.                    (L.2)
```

After a crossing of length `m log(p)`, (L.2) has the desired finite-prime Weil
coefficient. It is not the full one-crossing principal part of the positive
owner. Proof 206 shows that the difference already leaks another one-step
crossing at order `a^2`, before any summability or domain question.

## Route obligation

```text
route obligation:
  construct one positive finite-S owner whose direct crossings are exactly
  the selected p^m Weil atoms and whose interrupted words form a same-domain
  compact post-Q remainder

old weak path:
  CCM24 metric H=(I-aU)^*(I-aU), whose endpoint projection doubles p^2

new mathematical owner:
  none; the inverse-log metric candidate is rejected by proof 206

consumer to rewire:
  none; Plan 032 Gate 3 remains on the old active path

forbidden circular inputs:
  stored finite-S positivity, stored trace read-off, stored compactness,
  global Weil positivity, either RH-level route root, or a formal quotient
  that silently deletes one-boundary terms

smallest verification target:
  the one-prime (-1,0) translation-fiber entry in proof 206

focused axiom audit:
  deferred; no Lean declaration is introduced before the ideal/domain gate
```

## Positive metric

Each `U_p` is unitary and the finite family commutes because every `U_p` is a
function of the same scaling generator. On a scalar phase,

```text
ell_p(theta)
  = 2 log|1-a_p exp(i theta)|
  <= 2 log(1+a_p).                                      (L.3)
```

Functional calculus and finite summation give

```text
ell_S <= b_S I,
(1+b_S)I-ell_S >= I.                                   (L.4)
```

The operator in (L.4) is also bounded above because `S_f` is finite and
`a_p<1`. Hence its inverse exists and

```text
0 < H_S <= I.                                           (L.5)
```

Let `T_S=H_S^(1/2)`. For the archimedean Sonin projection `R`, define

```text
A_S=R H_S R | Ran(R),
R_S=T_S R A_S^(-1) R T_S.                              (L.6)
```

The lower spectral bound on `H_S` makes `A_S` boundedly invertible. Formula
(L.6) is the orthogonal projection onto `T_S Ran(R)`, so for every legal test
convolution `C_g`,

```text
Tr(C_g R_S C_g^*) >= 0.                                 (L.7)
```

This range is genuinely different from the transported CCM24 Sonin range.
Proof 124's same-range uniqueness theorem therefore does not apply.

## Exact trace split

The test convolution commutes with `T_S` and `H_S`. Under the same
bounded/trace-class cyclicity used in proof 042, for `C_f=C_g^* C_g`,

```text
L_S(f)
 := Tr(C_g R_S C_g^*)
  = Tr(C_f H_S R A_S^(-1)R)
  = Tr(C_f R)
    + Tr(R C_f Q H_S R A_S^(-1)).                      (L.8)
```

The first term is exactly the archimedean Sonin positive trace. No scalar
normalization of `H_S` changes this bulk term.

## Direct crossing calculation

Write

```text
H_S=I+V_S.
```

By (L.5), `V_S` is self-adjoint and `||V_S||<1`. On `Ran(R)`,

```text
A_S=R+R V_S R,
A_S^(-1)=sum_(k>=0)(-R V_S R)^k.                        (L.9)
```

Therefore the finite-place factor in (L.8) is

```text
X_S
 := Q H_S R A_S^(-1)
  = Q V_S R * sum_(k>=0)(-R V_S R)^k.                  (L.10)
```

Replace each internal `R` in (L.10) by `I-Q`. The unique term with no
additional `Q` is

```text
X_S,direct
  = sum_(k>=0)(-1)^k Q V_S^(k+1)R
  = Q V_S(I+V_S)^(-1)R
  = Q(I-H_S^(-1))R.                                    (L.11)
```

The scalar term in `H_S^(-1)` disappears because `Q I R=0`. Equations
(L.1) and (L.11) then give

```text
X_S,direct=Q ell_S R.                                   (L.12)
```

Every other term from `R=I-Q` contains an additional internal `Q`. The original
proposal treated that syntactic fact as a second boundary transition. This is
the invalid step: the scalar Fourier component of `V_S` can sit next to that
compression and leave a genuine one-step translation block. Proof 206 makes
the leak explicit.

## Prime-power coefficients

For `a_p<1`, continuous functional calculus gives the norm-convergent series

```text
ell_p
  = log(I-a_p U_p)+log(I-a_p U_p^*)
  = -sum_(m>=1) a_p^m/m * (U_p^m+U_p^(-m)).             (L.13)
```

Substituting (L.13) into (L.12) proves (L.2). In particular,

```text
m=1: coefficient -a_p,
m=2: coefficient -a_p^2/2.                              (L.14)
```

The second line is the missing factor `1/2` in proof 042. The existing
single-crossing trace theorem supplies interval length `m log(p)`, so

```text
(a_p^m/m) * m log(p)=p^(-m/2) log(p).                   (L.15)
```

Because `ell_S` is a sum over primes, (L.12) contains no mixed-prime direct
word. Mixed-prime products arise only from the inverse expansion (L.10), where
they carry an additional boundary interruption.

## Failed analytic gate

The required theorem would have been:

```text
X_S-X_S,direct
  factors into absolutely trace-norm summable words with at least two
  smoothed Sonin boundary crossings;

post-Q of that sum
  is one compact self-adjoint operator on the same root space;

L_S(f)
  = selected QW(f) + the named post-Q remainder.
```

It is false for this candidate. In the one-prime half-line model, proof 206
derives

```text
X_S-X_S,direct
  = a^2(2 Q(U+U*)R+Q(U+U*)Q(U+U*)R)+O(a^3).
```

The first summand is a nonzero one-step crossing of infinite multiplicity on
the continuous translation fibers. Weighted Wiener summability controls
coefficient tails; it cannot change this principal operator block into a
two-crossing trace-class word.

## Source and repository evidence

```text
CCM24 semilocal Sonin metric and transport:
  arXiv:2310.18423v2, mainc2m24fine.tex:946-1029

CC20 positive Sonin trace and smoothing:
  arXiv:2006.13771, weil-compo.tex:1178-1199, 2105-2120

endpoint projection trace algebra and rejected p^2 coefficient:
  docs/proofs/042_metric_sonin_second_prime_power_rejection.md

single-crossing trace read-off:
  docs/proofs/038_single_crossing_weil_read_off.md

multi-crossing ideal estimates to be adapted:
  docs/proofs/037_metric_sonin_ideal_closure.md
```

Primary sources:

```text
https://arxiv.org/abs/2310.18423
https://arxiv.org/abs/2006.13771
```

## Verdict

```text
positive bounded metric: passed
positive orthogonal-projection owner: passed
archimedean bulk preserved once: passed
formal no-internal-Q coefficients: a^m/m
intrinsic all-prime-power channel: failed
single-crossing leak: present at order a^2
interrupted-word trace-class factorization: false
Plan 046: rejected by proof 206
Lean owner: forbidden
RH: unproved
```
