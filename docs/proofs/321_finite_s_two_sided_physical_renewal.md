# Proof 321: finite-S two-sided physical renewal

## Result

The normalized finite-S Gate 3U owner now has an exact operator-norm renewal
expansion on the actual common-log carrier.  The construction keeps the
transported-Sonin orthogonal projection between the two Euler translations:

```text
c_S T_S^* P_(T_S Sonin) c_S (T_S^-1)^*
  = sum_forward sum_inverse
      signed_weight(left,right)
      U_(left) P_(T_S Sonin) U_(right).
```

After the source Sonin complement and selected detector are inserted, the
same expansion is the complete normalized physical response.  The source
Sonin complement is not split during estimation, so its outer-boundary,
second-support, and prolate contributions remain recombined.

## Construction

`CCM24FiniteSMultiRenewal.lean` upgrades the inverse renewal from a pointwise
vector formula to an absolutely convergent operator series and then takes its
adjoint.  The adjoint series uses the genuine positive logarithmic
translations.

`CCM24FiniteSForwardRenewal.lean` proves the finite signed Boolean expansion
of `c_S T_S^*`.  Each visible prime contributes either the identity or the
negative translated Euler term.

`CCM24FiniteSTwoSidedOperatorExpansion.lean` inserts the actual transported
Sonin projection.  It proves operator-norm summability on the inverse side and
does not commute the projection through either translation.

`CCM24FiniteSTwoSidedIndexBridge.lean` identifies the operator index
`(forward choices, inverse counts)` with one `(Bool, Nat)` coordinate per
visible prime.  Under this equivalence:

```text
total displacement = left displacement + right displacement
absolute signed coefficient = normalized two-sided scalar weight.
```

`CCM24FiniteSPhysicalRenewalExpansion.lean` inserts the recombined source
Sonin complement, selected convolution detector, and source compression.  It
proves the exact expansion for both the normalized physical leakage and the
normalized source response.

## Remaining Gate 3U bottom

This proof does not establish compact-displacement truncation of the scalar
trace atoms.  The operator atoms contain

```text
U_(left) P_(T_S Sonin) U_(right),
```

and `P_(T_S Sonin)` is not translation invariant.  Therefore compact support
of the convolution root does not permit replacing the atom by a single
translation of displacement `left + right`.

The next required producer is source-specific: after the complete physical
boundary and detector trace pairing, prove that the signed scalar atom
vanishes when its total displacement exceeds the root support radius.  Only
then can `CCM24FiniteSSupportMajorant.lean` supply the existing finite-S
independent bound

```text
7 ^ (ceil (exp B) + 1).
```

Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.
