# Proof 672: radial reduction of frame-loss commutator

## Result

The result is good as an exact carrier reduction, but it does not provide the
radial graph estimate itself. The module proves that the actual semilocal
Sonin projection is contained in the genuine upper radial-support projection
and that the positive prime-log translation is triangular with respect to this
support split.

Let

```text
E   = radialSupportProjection unitSoninScale
F   = I - E
P_S = newSuffixRangeProjection unitSoninScale S
U_p = (cc20GlobalLogTranslation (log p)).toContinuousLinearMap.
```

The proved identities are

```text
E P_S = P_S = P_S E,
F P_S = 0 = P_S F,
E U_p F = 0.
```

The last identity is obtained by adjointing the fact that the negative
translation preserves the upper radial half-line. Therefore

```text
P_S U_p F = 0,
```

and the actual commutator depends only on the upper radial input:

```text
[U_p, P_S] E = [U_p, P_S].
```

The same triangularity gives the denominator readout

```text
E (I + U_p) E = E (I + U_p).
```

## Radial producer contract

The new route-uniform predicate is the source-specific compressed estimate

```text
||[U_p, P_S] (E u)||
  <= L * ||E (I + U_p) (E u)||
```

for every visible prime `p`, every route-valid suffix `S`, and every
`u : finiteSCarrier`. This is a real producer obligation; no numerical value
of `L` is asserted here.

## Consumer handoff

Once the radial contract holds, the module proves the full relative estimate

```text
||[U_p, P_S] u|| <= L * ||(I + U_p) u||.
```

The proof uses the exact commutator absorption above and contractivity of the
orthogonal projection `E`. It then feeds the existing Proof 671 consumers:

```text
raw Bone 1 bound B + relative bound L
    -> ambient loss factor B * (L + 1)
    -> Proof 669 two-step factor
    -> paired finite-horizon envelope.
```

No extra norm constant is introduced by the radial reduction. The only `+1`
is the contractive projection term already present in Proof 671.

## Remaining gap

The radial estimate is still the active source-specific lower-level theorem.
Ordinary boundedness of `[U_p, P_S]` is not enough: the denominator
`(I + U_p)u` can be small on antiresonant approximate-kernel vectors. A proof
must preserve that cancellation in the complete support/Fourier/prolate
operator, uniformly over route-valid `(p,S)`. Gate 3U, the finite-S sign,
Burnol's identity, and RH remain open.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialReduction.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialReductionAudit.lean
```

The source is imported by `ConnesWeilRH/Source/CCM25Concrete.lean`.
