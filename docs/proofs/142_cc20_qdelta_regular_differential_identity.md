# CC20 Q-Delta Regular Differential Identity

Date: 2026-07-12

Status: accepted scalar differential identity on `rho > 1`; not yet a kernel
action theorem and not an RH proof.

## Result

The Lean source now defines the multiplicative-coordinate operator

```text
multiplicativeQ f rho =
  -(rho * deriv f rho + rho^2 * deriv (deriv f) rho) + f rho / 4
```

and proves

```text
multiplicativeQ_cc20DeltaRegular_of_one_lt :
  1 < rho ->
  multiplicativeQ cc20DeltaRegular rho = cc20QDeltaRegularCandidate rho
```

The proof is built from audited first and second derivatives of the two
sine-integral quotient branches, the inverse-square-root derivative, and the
second-order product rule.

## Verification

The isolated WSL2 ext4 source build and import-facing audit pass. The final
differential identity depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

## Remaining gate

This theorem identifies an ordinary one-variable scalar on the non-diagonal
region. It does not yet prove that

```text
k_I(u,v) = cc20QDeltaRegularCandidate(max(u/v,v/u))
```

is measurable, square-integrable with the correct multiplicative measure, or
acts as the CC20 compact remainder. The diagonal Dirac term remains separate.

## Route judgment

```text
regular Q(delta) scalar identity: accepted for rho > 1
two-variable kernel: open
Hilbert-Schmidt estimate: open
kernel-action identity: open
RH: unproved
```
