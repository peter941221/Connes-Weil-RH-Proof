# 1620 — The S3 reduction layer is complete: one open estimate in five equivalent forms

Date: 2026-09-18.

Status: route record. Zero new Lean this wave by design (the brick registered
for this face is already in the tree, law F8). S3 remains OPEN.

Consumer (named): the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)); S3 is the WO-S
brick of map [042](../map/042_g8_diagonal_leg_operator_bridge_audit.md).

## 1. The committed chain, quoted

`ConnesWeilRH/Dev/C1G8R3GateAmbientNormalForm.lean` proves the whole
equivalence chain, every link standard-axiom, no `sorry`:

| Link | Declaration | Statement |
| :-- | :-- | :-- |
| 1 | `gateAmbient_iff_sourceGate_squareSum` (`:102`) | source gate `J† C J` ⟺ ambient conjugate `P C P` columns, any named bases (1503 section 2 normal form) |
| 2 | `sourceGate_squareSum_iff_sourceInputEnergy` (`:156`) | gate ⟺ full detector energy `C ∘L J` (consumes the committed Sonin leakage square-sum, record 1497) |
| 3 | `sourceGate_squareSum_iff_hardyCompressedRootEnergy` (`:195`) | gate ⟺ Hardy-compressed root `E Q E C J` (all-scale prolate factor is HS, so the correction is removed) |
| 4 | `hardyCompressedRootEnergy_eq_sourceProjection_add_prolateRemainder` (`:289`) | exact operator identity `E Q E C J = P C J + R C J` |
| 5 | `hardyCompressedRootEnergy_squareSum_iff_sourceProjectionRootEnergy` (`:309`) | Hardy-compressed ⟺ source-projection leg `P C J` |

with `C = rootConvolution owner`, `J = sourceInclusion λ`,
`P = sourceSoninProjection λ`, `E = radialSupportProjection λ`,
`Q = sourceFourierSupportProjection λ`, `R = sourceProlateRemainder λ`.

The operator-level layer is records
[1614](1614_s3_operator_target_boundary.md)–[1617](1617_source_compressed_root_kernel_one_sided.md):
the ambient non-Hilbert–Schmidt obstruction blocks only the ambient shortcut
(1614); the direct kernel route on the source carrier (1615); the exact
prolate split (1616); and the one-sided compression
`J† C J = J† (E Q E) C J − J† R C J` (1617) that removes the second Hardy
corner from the producer target.

## 2. Equivalence table of the open estimate

```text
+----+--------------------------------+------------------------------------------+
| #  | form                           | object                                   |
+----+--------------------------------+------------------------------------------+
| i  | ambient HS gate (1508)         | P ∘L C ∘L P, any named ambient basis     |
| ii | source-compressed gate         | J† ∘L C ∘L J on a named source basis     |
| iii| source-input energy            | C ∘L J                                   |
| iv | Hardy-compressed root          | E ∘L Q ∘L E ∘L C ∘L J                    |
| v  | source-projection root energy  | P ∘L C ∘L J                              |
+----+--------------------------------+------------------------------------------+
```

Links 1–5 make i ⟺ ii ⟺ iii ⟺ iv ⟺ v, and 1617's one-sided form adds
`J† C J = J† (E Q E) C J − J† R C J` with the prolate term already controlled.
Every form carries the same single analytic content; the differences between
them are exactly the already-formalized reductions, not new freedom.

## 3. Verdict on further algebraic work

The reduction layer has consumed its algebra. Any further brick that
rearranges these five forms is a rename of the same estimate (law F8), so the
S3 spend for this wave is zero and the record exists to say why. The
remaining content is analytic: one square-sum estimate for the committed
object, in any of the five shapes. Guardrails that stay active:

- no Friedrichs-angle gap ([015](../map/015_r3_weighted_two_projection_trace_bridge.md),
  [016](../map/016_r3_endpoint_spectral_measure_audit.md); the angle branch was
  retired by record 1587);
- no ambient Hilbert–Schmidt shortcut
  ([1512](1512_hs_orthonormal_obstruction.md),
  [1614](1614_s3_operator_target_boundary.md));
- no premise presumes a `qw` sign, `SourceRH`, or a universal gate
  ([012](../map/012_g8_same_owner_readback_rh_reachability.md) section 3).

The adjacent bricks landed this wave are B4-side and carrier-side
([1619](1619_strip_confinement_landed_signed_b4_target.md),
[1621](1621_carrier_eigenvector_bridge_and_t4_route.md)); they narrow the
geometry and the base of the face but neither is an S3 estimate. S3, WO-S,
WO-B, ρ5, R4/(OB)/W1 and RH are unchanged and open.