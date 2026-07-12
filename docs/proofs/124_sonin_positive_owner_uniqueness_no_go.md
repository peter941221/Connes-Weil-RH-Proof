# 124 Sonin Positive-Owner Uniqueness No-Go

Date: 2026-07-12

## Result

Within the source-backed semilocal Sonin range, positivity and exact removal
of the archimedean bulk uniquely force the endpoint metric projection.  That
projection has the fatal factor-two `p^2` coefficient proved in record 042.
Changing only the positive weight on the same range cannot reopen the route.

## Source Range

For one finite prime, CCM24 gives the bounded invertible multiplier

```text
T_a = I-aU,  a=p^(-1/2),
H_a = T_a* T_a,
```

and transports the archimedean Sonin range `Ran(R)` to

```text
M_a = T_a Ran(R).
```

On `Ran(R)`, put

```text
A_a = R H_a R | Ran(R).
```

The density bounds for `H_a` make `A_a` positive and boundedly invertible.

Source: CCM24, arXiv:2310.18423v2, `mainc2m24fine.tex:946-1029`.

## Positive Same-Range Family

Every bounded positive owner obtained from the same transported range and a
positive functional-calculus weight has the form

```text
B_a(phi) = T_a R phi(A_a) R T_a*,
phi(A_a) >= 0.
```

For a commuting test convolution `C_f`, bounded/trace-class cyclicity gives

```text
Tr(C_f B_a(phi))
  = Tr(C_f H_a R phi(A_a) R).
```

Use

```text
H_a R = R H_a R + (I-R)H_aR = A_a + QH_aR.
```

The trace splits exactly as

```text
Tr(C_f B_a(phi))
  = Tr(C_f A_a phi(A_a) R)
    + Tr(R C_f Q H_a R phi(A_a) R).                    (U.1)
```

The first term is the same-range bulk.  The second term contains the Sonin
boundary crossing where a finite-prime read-off could occur.

## Uniqueness

The source archimedean positive trace is `Tr(C_f R)`.  At the operator-owner
level, requiring (U.1) to have that exact bulk forces

```text
A_a phi(A_a) = I on Ran(R).
```

Because `A_a` is invertible,

```text
phi(A_a) = A_a^(-1).
```

A weaker claim that only the traces agree for the selected test family needs
a separate theorem proving that this family annihilates or separates
`A_a phi(A_a)-I`.  No source theorem supplies such a cancellation.  Storing it
as a trace read-off premise would merely rename the missing no-bulk theorem.

Consequently

```text
B_a(phi)
  = T_a R A_a^(-1) R T_a*,
```

the unique orthogonal projection onto `M_a`.  This is exactly the endpoint
metric Sonin projection analyzed in records 034--042.

If `A_a phi(A_a) != I`, the first term of (U.1) leaves an additional
same-range multiplier bulk.  It is not a compact boundary correction.  Making
that bulk positive while retaining the signed Euler logarithm reintroduces the
scalar-compensation obstruction of records 115--118.

## Consequence For Spectral Projections

Suppose a proposed semilocal negative spectral projection has range equal to
`M_a`.  Orthogonal-projection uniqueness identifies it with the rejected
metric projection.

If its range differs from `M_a` only by a finite-dimensional or compact
correction, that correction cannot remove the excess `p^2` single-crossing
partial translation, which is noncompact before test smoothing.

Therefore a viable spectral owner must differ noncompactly from the CCM24
Sonin range and must prove a new same-object trace identity from scratch.  It
cannot be justified only by Sonin transport, equivalent norms, or a different
positive weight on the same range.

## Verdict

```text
same Sonin range + positivity + exact archimedean bulk:
  uniquely the endpoint metric projection

endpoint metric projection:
  rejected by the p^2 factor-two theorem

same range with another positive weight:
  leaves a noncompact multiplier bulk

compact/finite-rank range correction:
  cannot repair the noncompact excess channel

Lean owner:
  forbidden for this family

RH:
  unproved
```

The only possible finite-S reopening now requires a genuinely different
noncompact range together with its own common-domain positive trace and exact
Weil read-off.  No checked primary source currently supplies that theorem.
