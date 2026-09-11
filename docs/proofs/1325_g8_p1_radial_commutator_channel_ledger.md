# 1325 — G8 P1 radial commutator channel ledger

Date: 2026-09-11.

Status: FORMAL Lean brick. It packages the exact radial-side commutator
split into a two-channel ledger with closed constants. It proves no smallness
of either channel, no vanishing, no metric-to-radial transport, and no RH
statement.

## Statement

On `finiteSCarrier`, the frame-loss commutator splits exactly (existing
source identity)

```text
[U_p, P_S] = [E U_p E, P_S] + (I - E) U_p P_S.
```

Lean now proves the quantitative dual of the metric-side projection-defect
ledger:

1. interior channel: `|| [E U_p E, P_S] || <= 2` (translation is an isometry,
   both radial projections are contractions, and a commutator costs
   `2 ||P|| ||W||`);
2. boundary channel, pointwise for all `u`:
   `|| (I - E) U_p P_S u || <= (32 ||q_p^{-1}||) * || newFrameAntiresonantColumn p S (frame† u) ||`;
3. ledger: `|| [U_p, P_S] u || <= 2||u|| + (32 ||q_p^{-1}||) * || antiCol (frame† u) ||`;
4. operator-norm corollary:
   `|| [U_p, P_S] || <= 2 + (32 ||q_p^{-1}||) * || antiCol ∘L frame† ||`.

The inverse Euler coefficient stays visible throughout; the ledger is not a
uniform bound in `p`.

## Lean owner

`C1G8P1RadialCommutatorChannelLedger.lean`, paired audit declarations:

```text
norm_radialCompressedPositiveTranslation_le_one
norm_radialInteriorSoninCommutator_le_two
norm_radialSoninBoundaryCrossing_apply_le_canonical_antiresonantColumn
norm_suffixPrimeTranslationProjectionCommutator_apply_le_twoChannel
norm_suffixPrimeTranslationProjectionCommutator_le_twoChannel
```

## Verification

Batch `1538_g8_p1_radial_transport_batch_retry11.log`: 4074 jobs, zero
`error:` and `sorryAx`; every audit declaration prints only
`[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
