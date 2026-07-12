# 085 Xi Rescue Versus Current Source Owner

Date: 2026-07-12

## Cheap death result

The fixed-interval joint-separation argument in proof 084 cannot currently be
instantiated in the repository's source owner.

`SourceTestAlgebra` (`ConnesWeilRH/Source/AnalyticCoreBase.lean:109`) stores only
a carrier type, an equivalence to legacy test functions, and operations
`convolutionStar`/`involution`. It provides no additive group, scalar action,
or linear-combination constructor on the carrier. Therefore the finite witness
combination produced by the abstract linear-dual argument is not a source test
object.

The only concrete carrier used by the current Yoshida path is
`SourceConcreteBaseLayer.concreteTestAlgebra`. Its star convolution is literally
`f + g`, as exposed by
`normalizedCC20TestSpace_is_additive_pole_model` in
`ConnesWeilRH/Source/CC20ConcreteTestSpace.lean`. The repository proves this
model is semantically invalid for the required source convolution:

```text
not_normalizedCC20MellinConvolutionLaw
```

in `ConnesWeilRH/Source/CC20YoshidaConstruction.lean:2727` constructs a finite
Mellin test with value `1`; the additive operation doubles it to `2`, whereas
genuine Mellin multiplicativity would require `1 * 1 = 1`.

## Consequence

The 083 rescue currently has no admissible same-object owner:

```text
abstract C_c^infinity linear witnesses: available
current source carrier: no linear structure
current concrete carrier: linear-looking but Mellin-invalid
```

Adding a linear structure to `SourceTestAlgebra` without replacing the
additive toy convolution would only hide the mismatch. A valid reopening needs
a new source-backed multiplicative convolution carrier with:

1. finite complex linear combinations of compact smooth tests;
2. Mellin multiplicativity for `convolutionStar`;
3. support and involution transport;
4. the same CC20 trace and CCM25 Weil read-off objects.

Until that owner exists, the Xi quotient plus bad-space rescue remains a sound
analytic idea but is not an executable project route. No Lean wrapper should be
added for it.

