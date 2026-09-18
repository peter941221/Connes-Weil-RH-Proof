# 1618 — Route re-review before the S3 / B4 / carrier wave

Date: 2026-09-18.

Verdict: preflight. Zero new Lean, zero digits; it fixes what the wave may
spend on and records three re-aiming decisions.

Consumer (named as map README requires): the same-owner healthy-`CompactLog`
B5 statement `0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)); the binding
route [003](../map/003_b1_b5_minimal_exit_route_selection.md) is unchanged.

## Item 1 (S3): the planned brick is already landed

The registered next S3 brick — "bring the 019–024 leakage/common-right legs
onto the source-compressed form" — is already in the tree as a complete chain
of equivalences, `ConnesWeilRH/Dev/C1G8R3GateAmbientNormalForm.lean`, with the
operator-level boundary audits of records
[1614](1614_s3_operator_target_boundary.md)–[1617](1617_source_compressed_root_kernel_one_sided.md).
Writing another algebraic brick would duplicate committed material (law F8).
Decision: no S3 Lean this wave; the route record is
[1620](1620_s3_reduction_layer_complete.md).

## Item 2 (B4): the signed target is already reduced; the strip identity was not

Record [1599](1599_b4_unbounded_reflected_tail_boundary.md) typed the B4 tail
`H (I − E_w) H A` as an unbounded reflected half-line problem, and records
[1612](1612_source_column_wide_support_bridge.md)/[1613](1613_fourier_gap_b4_consumer.md)
already reduced the committed consumers to a wide-Hardy / wide-Fourier
certificate. What had never been landed is record
[1575](1575_Mp_support_ledger_hM_prime_verdict.md) section 3.3's strip
identity itself, plus its additive-shift composition form. Decision: land
exactly that, as pure support algebra, with no estimate — see
[1619](1619_strip_confinement_landed_signed_b4_target.md).

## Item 3 (carrier): the base object is a definition, not a theorem

`archimedeanSoninCarrier_nontrivial` is a `noncomputable def … : Prop`
(`ConnesWeilRH/Dev/SoninWindowWitness.lean:44`) and the committed source layer
consumes it as a hypothesis (`(hsource : ∃ y, y ≠ 0)`,
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSFixedFullBoundaryInjectivityGuard.lean:103`),
so the record-1586–1589 chain is conditional (law F33). Decision: instead of
another reduction, re-type the obligation as a fixed-point problem for the
committed Hardy–Titchmarsh involution and record the paper-level half-phase
computation that connects it to the classical Sonin/de Branges form — see
[1621](1621_carrier_eigenvector_bridge_and_t4_route.md). The de Branges
reading of the base obligation itself is record
[1590](1590_carrier_base_obligation_is_a_de_branges_existence_and_1331_erratum.md).

## Guardrails checked before spending

- No Friedrichs-angle gap is assumed anywhere in the wave
  ([015](../map/015_r3_weighted_two_projection_trace_bridge.md),
  [016](../map/016_r3_endpoint_spectral_measure_audit.md)).
- No ambient Hilbert–Schmidt shortcut: the ambient leakage/band-root
  obstructions ([1488](1488_r3_leakage_orthonormal_translation_orbit.md),
  [1489](1489_r3_leakage_orthonormal_orbit_energy_obstruction.md),
  [1512](1512_hs_orthonormal_obstruction.md)) and the exact target audit
  [1614](1614_s3_operator_target_boundary.md) stand.
- No premise presumes a `qw` sign, `SourceRH`, or a universal gate
  ([012](../map/012_g8_same_owner_readback_rh_reachability.md) section 3 stop
  rule).
- Strip confinement is support algebra, not singular-value content: the
  strip-restricted square-sum stays unpriced ([1579](1579_g8_survivors_adjudicated_hradial_priced_and_support_lemma_committed.md),
  law F29; the strip count of [1585](1585_indicator_hs_erratum_and_strip_escape_identity.md)).

## Acceptance

One focused build for the whole wave:
`build-logs/1618_strip_confinement_carrier_bridge.log` — 4076 jobs,
`Build completed successfully`, zero `error:` lines, zero `sorryAx`, 14
standard `[propext, Classical.choice, Quot.sound]` axiom prints (9 strip
confinement + 5 carrier bridge), no warning attributable to the new modules.