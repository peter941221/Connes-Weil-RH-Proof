# Proof 674: support and norm readout for the radial boundary channel

## Result

The result is good as a genuine support/norm producer, but it does not prove
the antiresonant graph estimate. Proof 674 generalizes the existing radial
crossing readout from new-frame vectors to every input in the actual upper
radial support.

For `u` in the support of
`E = radialSupportProjection lambda`, the positive translation satisfies

```text
((I-E) U_(log p) u)(t)
  = 1_[log(lambda)-log(p), log(lambda))(t) * u(t + log(p))
```

almost everywhere on the genuine whole-line `L2` carrier. The proof uses the
literal support predicate, the actual additive Haar/log translation, and the
translated half-line projection; it is not a finite-dimensional or surrogate
model statement.

## Actual suffix specialization

Because Proof 672 proves `E P_S=P_S` for the actual suffix Sonin projection,
the generic readout specializes to the signed boundary channel

```text
C_(p,S)^bdry = (I-E) U_(log p) P_S.
```

The same finite radial interval appears, with the input read as
`P_S v (t + log(p))`. This is the support fact needed before applying a
compact-root support restriction; it does not identify the channel with the
new-frame column or with the complete physical interior owner.

The norm producer is

```text
|| (I-E) U_(log p) u || <= ||u||,
|| C_(p,S)^bdry v || <= ||P_S v|| <= ||v||.
```

The first inequality is projection contractivity plus translation isometry;
the second adds contractivity of the actual semilocal Sonin projection.

## Remaining gap

Proof 674 supplies no bound relative to `||(I+U_p)u||`. The active source
obligation remains the signed graph estimate for the sum from Proof 673:

```text
||[U_p,P_S](E u)||
  <= L * ||E (I + U_p) (E u)||,
```

uniformly over route-valid `(p,S)`. Gate 3U, the finite-S sign, Burnol's
identity, and RH remain open.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySupport.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySupportAudit.lean
```

The source is imported by `ConnesWeilRH/Source/CCM25Concrete.lean`.
