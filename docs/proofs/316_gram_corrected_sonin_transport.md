# Proof 316: Gram-Corrected Sonin Transport

## Result

Let `S` be a closed source Sonin subspace and let `T` be a bounded invertible
transport between Hilbert carriers. Put

```text
A = T restricted to S.
```

The orthogonal projection onto the transported Sonin space is represented by

```text
R_T = A (A^dagger A)^(-1) A^dagger.
```

This is the corrected replacement for the illegal oblique similarity

```text
T P_S T^(-1).
```

## Algebra

For a general frame, write `Ginv=(A^dagger A)^(-1)` and use the exact
restricted Gram inverse identity

```text
Ginv A^dagger A = I.
```

Then

```text
R_T^2
 = A Ginv A^dagger A Ginv A^dagger
 = A Ginv A^dagger
 = R_T.
```

If `Ginv` is self-adjoint, then

```text
R_T^dagger=R_T.
```

Consequently `R_T` is a star projection. Its range is exactly `Ran(A)`, not
merely its closure:

```text
Ran(R_T)=Ran(A)=T(S).
```

## Lean Owner

The generic construction is in
`ConnesWeilRH/Source/CC20Concrete/GramCorrectedSoninTransport.lean`:

```text
gramCorrectedProjection
gramCorrectedProjection_isIdempotentElem
gramCorrectedProjection_isSelfAdjoint
gramCorrectedProjection_isStarProjection
gramCorrectedProjection_range
restrictedClosedTransport
restrictedClosedTransport_range
restrictedClosedTransportEquiv
restrictedTransportGramInv
restrictedTransportGramInv_leftInverse
transportedSoninStarProjection
transportedSoninStarProjection_isStarProjection
transportedSoninStarProjection_range
```

The focused audit entrypoint is
`ConnesWeilRH/Dev/GramCorrectedSoninTransportAudit.lean`.

## Verification

Verified on 2026-07-16 in a WSL2 Linux-side ext4 verification copy.

The focused command checks the generic frame theorem, the restricted
continuous linear equivalence, the constructed Gram inverse, the resulting
star projection, and their exact ranges:

```text
lake env lean ConnesWeilRH/Dev/GramCorrectedSoninTransportAudit.lean
```

It exits successfully. Every `#print axioms` result is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Integration through the public source aggregate also passes:

```text
lake build ConnesWeilRH.Source.CC20Concrete
```

The aggregate completes successfully with `3608` jobs and explicitly builds
`GramCorrectedSoninTransport`. A source and audit scan finds no `sorry` or
`admit`. The new source and audit introduce no linter warning. SHA-256 hashes
for the source, audit, and aggregate import file match the current Windows
worktree byte-for-byte.

## Why It Matters for CCM24

CCM24 Theorem 4.6 only makes `theta_S` a bounded invertible hilbertian map of
the Sonin spaces. Proof 316 uses that exact strength. It neither upgrades
`theta_S` to a unitary nor transports either support projection by similarity.

Source: https://arxiv.org/html/2310.18423v2

The Mathlib adjoint and star-projection APIs used by the construction are in:

```text
Mathlib.Analysis.InnerProductSpace.Adjoint
Mathlib.Analysis.InnerProductSpace.Projection.Basic
```

Sources:

* https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Analysis/InnerProductSpace/Adjoint.lean
* https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean

## Remaining Producer

The active Lean bottom is now concrete:

```text
construct the actual CCM24 theta_S
  -> restrict it to the source Sonin closed subspace
  -> identify Ran(A) with the actual semilocal Sonin intersection
  -> identify the resulting star projection with the target R_S
```

For any `ContinuousLinearEquiv T`, the generic layer now constructs

```text
E : S equivL T(S),
(E^dagger E)^(-1)=E^(-1)(E^(-1))^dagger,
```

and hence the transported star projection without an additional inverse
premise. The remaining inputs are the actual CCM24 `theta_S` and its
Sonin-space identification.

In Lean, the closed subspace carrier is `S.toSubmodule`, with completeness
installed from `S.isClosed.completeSpace_coe`. Rectangular continuous linear
maps are composed with `∘L`; multiplication `*` applies only to endomorphisms.
These type-level distinctions are part of the verified construction, not
notation-only details.

This still does not construct the actual semilocal support projection `P_S`,
the semilocal Fourier projection `Q_S`, compactness of the correction, or the
finite-S sign.

```text
RH = UNPROVED
```
