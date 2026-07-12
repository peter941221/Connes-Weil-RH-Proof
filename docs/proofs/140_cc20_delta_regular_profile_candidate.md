# CC20 Regular Delta Profile Candidate

Date: 2026-07-12

Status: accepted as an analytic candidate only; no route owner and no RH
conclusion.

## Object

`ConnesWeilRH/Source/CC20Concrete/RegularKernelCandidate.lean` defines

```text
cc20DeltaRegular rho =
  2 * sqrt(rho) *
    (Si(2*pi*(1+rho))/(2*pi*(1+rho))
     + Si(2*pi*(rho-1))/(2*pi*(rho-1)))
```

The two quotient terms are represented by the continuous integral-average
extension from proof 139. Thus the apparent `rho = 1` singularity is not
hidden in the definition.

The same module defines `cc20DeltaRegularDerivative` and proves
`hasDerivAt_cc20DeltaRegular` for `1 < rho`. The proof combines the nonzero
quotient derivative, affine chain rules, the square-root derivative, and the
product rule.

The module also records `cc20DeltaRegularSecondDerivative` and the explicit
non-diagonal `cc20QDeltaRegularCandidate` obtained from
`-(rho*d/drho)^2 + 1/4`. These are definitions only until the corresponding
second-derivative and kernel-action equalities are proved.

The auxiliary theorem `hasDerivAt_inv_sqrt` proves
`(1/sqrt rho)' = -1/(2*rho*sqrt rho)` for positive `rho`, removing the last
standalone square-root derivative gap in the full second-derivative product
rule.

## Verification

The isolated WSL2 ext4 snapshot passes:

```text
lake build ConnesWeilRH.Source.CC20Concrete.RegularKernelCandidate
lake env lean ConnesWeilRH/Dev/RegularKernelCandidateAudit.lean
```

`continuous_cc20DeltaRegular` has only the standard Mathlib axioms
`propext`, `Classical.choice`, and `Quot.sound`.

## Explicit non-result

This is the profile before applying `Q = -(rho d/drho)^2 + 1/4`. The project
still lacks:

```text
derivative formula -> q_reg
measurable two-variable kernel
L2 / Hilbert-Schmidt estimate
kernel-action identity
evaluation-space containment
```

The candidate is therefore not imported by any RH route consumer.

## Route judgment

```text
delta regular profile: accepted candidate
q_reg after Q: open
concrete K_I: open
RH: unproved
```
