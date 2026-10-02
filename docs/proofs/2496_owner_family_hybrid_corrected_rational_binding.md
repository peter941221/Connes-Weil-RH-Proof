# Record 2496 — corrected owner-family hybrid table binding

The corrected record-2495 replay is now materialized as the generated Lean
table `C1RouteAOwnerFamilyHybridTable2496.lean`.  The generator consumes the
640-cell payloads from
`results/2495_owner_family_hybrid_mpfr_exact.json`, checks the recorded
binary64 payloads, and emits exact rational literals.  The source artifact
SHA256 is:

`540f331cdbaaf83c06a25d7984a0a724fb06cf80bc777069fa45b016b465c1dd`

The Lean bridge
`C1RouteAOwnerFamilyHybridTableBridge2496.lean` exposes the same local
consumer shape as record 2494, but with the corrected table.  Its only
mathematical input is still the per-cell premise that the owner hybrid
curvature is bounded by the corresponding table payload.  The audit target
`C1RouteAOwnerFamilyHybridTableBridge2496Audit` builds successfully and the
audited declaration depends only on `[propext, Classical.choice, Quot.sound]`.

This record closes corrected payload provenance and Lean data consumption only.
It does not prove the directed analytic enclosure behind each payload, does
not close the selected-detector signed producer margin, and makes no RH claim.
The older 2492/2494 table remains historical and is superseded for corrected
pricing by 2496.
