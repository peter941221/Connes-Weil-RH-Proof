# 1498 — R3 survivor coframe source-carrier bridge (map 042 WO-S, S1+S2)

**Status: FORMAL.** New leaf
[`C1G8R3SurvivorCoframeBridge.lean`](../../ConnesWeilRH/Dev/C1G8R3SurvivorCoframeBridge.lean)
(+ paired audit `C1G8R3SurvivorCoframeBridgeAudit.lean`). Zero `sorryAx`;
axioms to be printed in the audit build below. RH is not claimed; no estimate
for the open leg is claimed.

## What is bridged

Map 042 [record](../map/042_g8_diagonal_leg_operator_bridge_audit.md) split the
survivor diagonal energy obligation `hSurvivor` (consumed by records
1485/1486/1493) into an in-Sonin (signal) half and an out-of-Sonin (leakage)
half, and left both open. This brick closes the *reduction* of both halves on
the source carrier:

* **S1 (factorization).** The survivor coframe factors exactly as
  `g8MetricSurvivorCoframe lambda family = u • (J ∘L s_S)` with the Euler upper
  factor `u = finiteEulerUpperFactor family.visiblePrimes > 0` and the purely
  source-side Schur leg
  `s_S = parameterizedSoninGramInvSqrt lambda 1 [] ∘L (transition†) ∘L parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes`
  (`g8MetricSurvivorCoframe_eq_smul_sourceInclusion_comp_survivorSourceLeg`).
* **S2 (exact pointwise split).** For every ambient vector
  (`g8BridgeSoninCarrier_normSq_split`, now on the ambient `finiteSCarrier`,
  coercion-free):
  `‖v‖^2 = ‖J† v‖^2 + ‖(I − P) v‖^2`,
  proven by the exact Pythagoras at `P = J ∘L J†` (committed
  `sourceInclusion_comp_adjoint`), orthogonality `J† (I − P) = J† − J† P = 0`
  (committed `sourceInclusionAdjoint_comp_sourceProjection` plus the star
  projection relation `P (I − P) = 0`), and
  `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`. No operator-norm input
  is used anywhere.

## The two energy directions

With the pointwise identity
`‖(C ∘L coframe) w‖^2 = |u|^2 (‖(J† ∘L C ∘L J) (s_S w)‖^2 + ‖((I−P) ∘L C ∘L J) (s_S w)‖^2)`
(`g8SurvivorCoframe_normSq_pointwise_split`), on any named source basis:

* **OUT free.** The leakage-band leg is the record-1497 selected-root
  source-Sonin leakage square-sum precomposed with the bounded `s_S`
  (`PositiveTrace.summable_normSq_precomp`), so it is square-summable with no
  hypothesis
  (`g8SurvivorSourceLeg_outLeg_normSq_summable_of_sourceSoninLeakage`).
* **Necessity.** `hSurvivor` implies the in-Sonin square-sum
  (`g8SurvivorSourceLeg_inLeg_normSq_summable_of_coframe_energy`), by the
  inverse-`|u|^2` domination.
* **Sufficiency.** The in-Sonin square-sum plus the free OUT leg reproduces
  `hSurvivor` (`g8SurvivorCoframe_energy_summable_of_inLeg`).

Hence the unconditional equivalence
(`g8SurvivorCoframe_energy_iff_sourceCarrier_inLeg`):

```text
hSurvivor  ↔  Σ_i ‖ (J† ∘L C ∘L J) (s_S (sourceBasis i)) ‖^2 .
```

## What this does and does not close

WO-S items S1 and S2 are landed as an exact operator identity; the remaining
survivor estimate is now the single in-Sonin source-carrier square-sum above.
That square-sum is still open — this brick supplies no bound for it. The
diagonal energy constraints (1485), the total metric trace limit (1486), the
trace-to-`qw` readback, and RH all remain open.
