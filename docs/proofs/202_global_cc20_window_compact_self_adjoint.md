# Proof 202: Global CC20 window compact self-adjoint owner

## Result

The ordinary CC20 regular-kernel operator on a finite logarithmic window now
has a genuine owner on the same whole-line Hilbert space used by the selected
finite-prime crossing sum.

For

```text
R_lambda : L2(R) -> L2([-log lambda, log lambda])
E_lambda : L2([-log lambda, log lambda]) -> L2(R),
```

the new declarations prove

```text
E_lambda^dagger = R_lambda,
R_lambda E_lambda = Id,
E_lambda R_lambda = P_lambda.
```

The finite-window Haar regular-kernel operator is self-adjoint by its already
proved real symmetric kernel. Its logarithmic conjugate `H_lambda` is compact
and self-adjoint. The global operator is then identified exactly as

```text
cc20GlobalLogWindowL2Operator lambda hlambda
  = E_lambda H_lambda E_lambda^dagger.
```

Consequently it is a genuine Mathlib `IsCompactOperator` and is
`IsSelfAdjoint` on `L2(R)`.

## Main declarations

```text
cc20LogWindowRestrictIndicatorCLM_eq_adjoint_restrict
cc20LogWindowRestrict_eq_adjoint_restrictIndicatorCLM
cc20LogWindowRestrictIndicator_comp_restrict
cc20WindowHaarComplexL2Operator_isSelfAdjoint
isCompactOperator_cc20GlobalLogWindowRestrictedL2Endomorphism
cc20GlobalLogWindowRestrictedL2Endomorphism_isSelfAdjoint
cc20GlobalLogWindowRestrictedL2Operator_eq_zeroExtension_comp
cc20GlobalLogWindowL2Operator_eq_zeroExtension_conjugation
isCompactOperator_cc20GlobalLogWindowL2Operator
cc20GlobalLogWindowL2Operator_isSelfAdjoint
```

## Why this matters

Before this result, the CC20 regular remainder lived only on a restricted
window carrier, while the finite-prime crossing operator sum lived on the
whole-line logarithmic carrier. Compactness on the restricted carrier did not
by itself justify treating the two operators as a same-domain sum.

The exact zero-extension conjugation removes that carrier mismatch. It is an
operator identity derived from the actual L2 restriction and indicator
extension, not a stored compatibility field.

## Verification

The Windows source snapshot was copied one way to the WSL ext4 verification
mirror. The focused build completed:

```text
lake build ConnesWeilRH.Source.CC20Concrete.GlobalLogKernel
2985/2985 jobs
```

The import-facing `GlobalLogHaarAudit.lean` checked, printed, and audited every
main declaration above. Each reports only:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, new `axiom`, or stored conclusion was introduced.

## Boundary

This does not prove the missing finite-S semilocal identity. In particular,
it does not prove that the ordinary CC20 regular-kernel operator is the
post-Q remainder paired with the selected whole-line crossing sum, and it
does not construct the genuine finite-S positive owner.

The remaining hard bottom is still

```text
genuine finite-S positive owner
  = exact selected single-crossing operator sum
    + same-domain post-Q remainder,
```

followed by the required sign on the route constraints. Common domain,
compactness, and self-adjointness are now available; the same-object semilocal
identity is not.
