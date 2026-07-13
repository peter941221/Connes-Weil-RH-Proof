# Proof 203: Selected finite-prime translation quadratic form

## Result

The selected finite-prime coefficients now have a direct quadratic-form owner
on the global logarithmic crossing Hilbert space. For one
`SelectedWeilSquareOwner`, the vector is the source test itself:

```text
sourceRootLp owner = owner.sourceTest.test.toLp 2.
```

The source-root correlation with a global translation is exactly the selected
convolution square:

```text
<sourceRootLp owner, T_b sourceRootLp owner>
  = owner.convolutionSquare.test b.
```

For a prime `p` and nonzero exponent `m`, define

```text
P_(p,m) = log(p) / sqrt(p^m) *
          (T_(m log p) + T_(-m log p)).
```

The translation covariance theorem gives `T_(-b) = T_b†`, so `P_(p,m)` is
self-adjoint. The same source root then reads off the existing selected
finite-prime atom without a stored trace premise:

```text
<sourceRootLp owner, P_(p,m) sourceRootLp owner>
  = owner.finitePrimeTerm (p^m).
```

Finite sums preserve self-adjointness and their quadratic form is the finite
sum of the corresponding finite-prime terms.

## Main declarations

```text
sourceRootLp
inner_sourceRootLp_translation_eq_convolutionSquare
primePowerTranslationWeight
primePowerTranslationOperator
primePowerTranslationOperator_isSelfAdjoint
inner_primePowerTranslationOperator_eq_finitePrimeTerm_pow
finitePrimeTranslationOperatorSum
finitePrimeTranslationOperatorSum_isSelfAdjoint
inner_finitePrimeTranslationOperatorSum_eq_finitePrimeTerm_pow_sum
```

## Why this matters

Proofs 198--202 identified the finite-prime main term through compact
Hilbert--Schmidt crossing factors and then assembled a compact whole-line
operator sum. This proof supplies the same arithmetic main term directly as a
quadratic form of the selected test root and the actual translation operators.
It removes ambiguity about which test and which convolution square carry the
finite-prime values.

The translation owner is intentionally not claimed to be compact. It is a
semantic quadratic-form bridge, not the missing finite-S positive owner. The
remaining hard bottom is still a genuine finite-S positive operator whose
single-crossing component is the already identified finite sum and whose
post-`Q` remainder has the required same-domain sign.

## Verification

The Windows source snapshot was copied one way to the WSL ext4 verification
mirror. The focused source build completed:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.SelectedPrimeTranslationQuadratic
2980/2980 jobs
```

The import-facing `SelectedPrimeTranslationQuadraticAudit.lean` checks and
prints all main declarations. Its axiom audit reports only:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, new `axiom`, or stored conclusion was introduced.

## Boundary

This result does not prove positivity, compactness, or the semilocal finite-S
remainder identity. In particular, it does not rewire
`unconditional_rh_skeleton`; the active route still needs the genuine positive
owner and its sign gate.
