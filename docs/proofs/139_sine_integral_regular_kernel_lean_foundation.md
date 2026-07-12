# Sine-Integral Regular-Kernel Foundation

Date: 2026-07-12

Status: accepted analytic foundation; not a CC20 kernel owner and not an RH
proof.

## Lean objects

`ConnesWeilRH/Source/CC20Concrete/SineIntegral.lean` defines

```text
sineIntegral x = integral_{0..x} Real.sinc(t)
sineIntegralQuotient x = integral_{0..1} Real.sinc(x*t)
```

The first object is continuous and satisfies the oriented interval difference
identity, and `deriv_sineIntegral` proves its derivative is `Real.sinc`. The
second is a continuous extension of the quotient `Si(x)/x`
with value `1` at `x = 0`; its integral-average definition avoids an
unproved removable-singularity convention. The theorem
`sineIntegralQuotient_eq_div` proves the expected quotient identity for every
nonzero real by an interval-integral change of variables.
The theorem `deriv_sineIntegralQuotient` then gives the quotient derivative at
every nonzero point by a local nonzero-neighborhood equality and the ordinary
quotient rule.

## Verification

In the isolated WSL2 ext4 verification snapshot:

```text
lake build ConnesWeilRH.Source.CC20Concrete.SineIntegral
lake env lean ConnesWeilRH/Dev/SineIntegralAudit.lean
```

Both passed. The audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for the continuity and interval identities.

## Remaining gate

The source expression for the CC20 regular remainder still needs:

1. a derivative formula for the full `cc20DeltaRegular` profile;
2. an explicit measurable `q_reg` after applying `Q` to the non-Dirac part;
3. a square-integrability proof and a kernel-action identity.

Until those are supplied, this module is only reusable scalar analysis.

## Route judgment

```text
regular sine-integral scalar: accepted
concrete K_I operator: open
evaluation-span containment: open
RH: unproved
```
