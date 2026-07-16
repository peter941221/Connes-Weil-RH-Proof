# Proof 317: CCM24 Sonin Projection Bridge

## Result

Proof 317 closes the operator-theoretic consumer after the actual CCM24
Sonin transport has been supplied.

Given source and target support subspaces, a bounded invertible map
`theta_S`, and the exact complete-intersection identity

```text
theta_S(source support intersection source Fourier support)
  = target support intersection target Fourier support,
```

the Gram-corrected transported projection is exactly the canonical target
orthogonal projection:

```text
A = theta_S restricted to the source Sonin intersection
R_gram = A (A^dagger A)^(-1) A^dagger
R_target = projection(target Sonin intersection)

R_gram = R_target.
```

The same target operator satisfies

```text
P Q P - R_gram = (P - R_gram) Q (P - R_gram)
IsPositive (P Q P - R_gram).
```

No unitary property of `theta_S` is assumed.

## Primary Source Evidence

CCM24 v2 defines the semilocal Sonin space in Definition 4.5. Section 4.6
uses `theta_S(f)` as the class of `sigma_S tensor f` and proves

```text
F_mu w_S(theta_S(f))(s)
  = (product over p in S without infinity of
       L_p(1/2 + i s))^(-1)
      F_mu w_infinity(f)(s).                         (58)
```

Section 4.7 proves `F_S theta_S = theta_S F_eR` and uses diagram (59)
to show that `theta_S` is bounded with bounded inverse. Theorem 4.6 states

```text
theta_S : S_lambda(R, e_infinity) -> S_lambda(X_S, alpha)
```

as a hilbertian isomorphism of complete Sonin spaces.

Primary source:
https://arxiv.org/html/2310.18423v2

These statements justify intersection-level transport. They do not state
that `theta_S` is unitary or that it conjugates either individual support
projection.

## Existing Model Boundary

The existing local source-model predicate has weaker semantics:

```text
SemilocalModelSymbols.soninSpaceComparison
  = supportInWindow sourceTest
      and FourierSupportInWindow sourceTest.
```

It is a support statement about one named test object, not an equality of
closed Hilbert subspaces. Likewise, the existing `boundedComparisonMap`
predicate hides an existential real-Hilbert self-equivalence; it does not
expose the two CCM24 Hilbert carriers or their Sonin subspaces.

Proof 317 does not coerce those weaker predicates into the stronger theorem.
The actual producer must instantiate new operator-level data directly.

## Lean Owner

`ConnesWeilRH/Source/CC20Concrete/CCM24SoninProjectionBridge.lean` defines

```text
CCM24SoninTransportData
sourceSoninClosedSubspace
targetSoninClosedSubspace
gramCorrectedTargetSoninProjection
targetSoninProjection
```

and proves

```text
transported_sourceSonin_eq_targetSonin
gramCorrectedTargetSoninProjection_isStarProjection
gramCorrectedTargetSoninProjection_range
gramCorrectedTargetSoninProjection_eq_targetSoninProjection
target_compression_sub_gramCorrected_eq_factor
target_compression_sub_gramCorrected_isPositive.
```

The data record deliberately has only one image field,
`maps_sonin_intersection`, and no fields asserting separate support
transport.

## Proof Flow

```text
+--------------------------------------------------------------+
| CCM24 producer obligations                                   |
|  actual source/target Hilbert carriers                       |
|  four closed support subspaces                               |
|  theta_S : bounded continuous linear equivalence             |
|  theta_S(source Sonin) = target Sonin                        |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Proof 316                                                    |
|  A(A^dagger A)^(-1)A^dagger is a star projection             |
|  with range theta_S(source Sonin)                            |
+------------------------------+-------------------------------+
                               | exact range equality
                               v
+--------------------------------------------------------------+
| Proof 317                                                    |
|  Gram projection = canonical target Sonin projection         |
|  target P Q P - R factorization and positivity               |
+--------------------------------------------------------------+
```

## Verification

```text
lake build ConnesWeilRH.Source.CC20Concrete.CCM24SoninProjectionBridge
Build completed successfully (2656 jobs).

lake env lean ConnesWeilRH/Dev/CCM24SoninProjectionBridgeAudit.lean

lake build ConnesWeilRH.Source.CC20Concrete
Build completed successfully (3609 jobs).

lake build
Build completed successfully (3661 jobs).
```

Every audited theorem reports exactly

```text
[propext, Classical.choice, Quot.sound].
```

## Remaining Producer

Proof 317 is a consumer bridge, not the missing CCM24 construction. The next
producer must construct in Lean:

```text
L2(R)^ev and L2(X_S)^(K_S),
the actual source and target support/Fourier-support closed subspaces,
theta_S as a ContinuousLinearEquiv,
the exact Theorem 4.6 Sonin intersection image equality.
```

It must not reuse the weaker one-test `soninSpaceComparison` predicate as
that equality.

Compactness, the rapid prolate spectrum, Gate 3U, the finite-S sign, Burnol's
identity, and the Riemann Hypothesis remain open.

```text
RH = UNPROVED
```
