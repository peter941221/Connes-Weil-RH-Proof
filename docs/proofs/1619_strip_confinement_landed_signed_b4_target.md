# 1619 — Strip confinement of the radial defect landed; the signed B4 target is a finite strip

Date: 2026-09-18.

Status: formal, accepted. Zero estimate; B4 remains OPEN at its producer
premise.

Consumer (named): the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)); B4 is the
WO-B internal-gap leg of map
[042](../map/042_g8_diagonal_leg_operator_bridge_audit.md).

## What landed

`ConnesWeilRH/Dev/C1G8R3StripConfinement.lean` with audit twin
`C1G8R3StripConfinementAudit.lean`, nine declarations, no `sorry`, standard
axioms only:

| Declaration | Content |
| :-- | :-- |
| `wideRadialScale_add` | the wide scale iterates additively |
| `wideRadial_support_comp` | composition of wide-certified factors |
| `radialComplement_comp_eq_wideProjection_sub` | defect = `E'' − E` |
| `radialComplement_comp_eq_stripProjection` | defect = translated interval projection on `[log λ − s, log λ)` |
| `radialComplement_comp_comp_eq_stripProjection` | same, source-column form `M ∘L J` |
| `radialComplement_apply_eq_strip_of_mem_wideRadial` | vector form |
| `suffixEulerFrameAmbientLossColumn_radialDefect_eq_strip` | committed column, width exactly `log p`, no caller premise |
| `suffixEulerFrameSchurStep_boundaryDagger_radialDefect_eq_strip` | committed dagger, width exactly `log p`, no caller premise |
| `hardyColumn_radialDefect_eq_strip_of_wideHardySupport` | signed Hardy-column corollary under the wide Hardy certificate |

The identity, verbatim: for `λ'' = λ·e^{−s}` (`s ≥ 0`) and any `M` with
`E_{λ''} ∘L M = M`,

```text
(1 − E_λ) ∘L M = (E_{λ''} − E_λ) ∘L M
               = T(−log λ) ∘L π_[−s,0] ∘L T(log λ) ∘L M .
```

This is record [1575](1575_Mp_support_ledger_hM_prime_verdict.md) section 3.3
landed as pure support algebra.

## Reading of the signed B4 target (1599)

[1599](1599_b4_unbounded_reflected_tail_boundary.md) typed the B4 tail
`H (I − E_w) H A` as an unbounded reflected half-line problem. The landed
corollary fixes what that tail is once the wide Hardy certificate holds — the
exact premise the committed gap consumer takes
([1612](1612_source_column_wide_support_bridge.md)/[1613](1613_fourier_gap_b4_consumer.md)):

```text
under  E_{λ''} ∘L H ∘L M ∘L J = H ∘L M ∘L J :
((1 − E_λ) ∘L H ∘L M) ∘L J
  = (T(−log λ) ∘L π_[−s,0] ∘L T(log λ) ∘L H ∘L M) ∘L J .
```

So the unbounded reach of `1 − E_λ` is exactly what the certificate removes:
the surviving defect is the finite strip `E_{λ''} − E_λ`, i.e. the width-`s`
ledger object of 1575 section 2 (one `log q` per adjoint Euler transport,
total `Σ log q`). The composition lemma carries the same shift indexing: since
the radial subspaces are nested, a composite inherits the certificate of its
outermost factor alone, and the sum-indexed form is the ledger shape.

Honest boundaries:

- The certificate itself is not proved for the actual visible-prime columns;
  it is the open B4 producer premise of 1612/1613. What changed is the
  geometry of the remainder, not its status.
- Strip confinement is support algebra, not singular-value content (law F29):
  the strip-restricted square-sum is unpriced
  ([1579](1579_g8_survivors_adjudicated_hradial_priced_and_support_lemma_committed.md),
  [1585](1585_indicator_hs_erratum_and_strip_escape_identity.md)). No decay,
  cancellation, Hilbert–Schmidt, or trace statement is supplied here.
- The `hgap` Fourier side of B4 is untouched; WO-S and WO-B statuses are
  unchanged.

## Acceptance

Build log: `/home/peter/rh/build-logs/1618_strip_confinement_carrier_bridge.log`
(shared with [1618](1618_route_rereview_s3_b4_carrier.md)/[1620](1620_s3_reduction_layer_complete.md)/[1621](1621_carrier_eigenvector_bridge_and_t4_route.md)).
`Build completed successfully (4076 jobs)`, zero `error:` lines, zero
`sorryAx`, 14 standard axiom prints (9 here + 5 carrier bridge), no warning in
the new modules.