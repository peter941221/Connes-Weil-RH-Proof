# Record 2694 - off-diagonal owner entry (13,3) membership

Status: FORMAL ENTRY MEMBERSHIP GREEN; 49 PARAMETERIZED OFF-DIAGONAL ENTRIES.

The degree-55 phase-carrying entry `(13,3)` is certified against the analytic
interval table:

```text
entry1303Mem2663 :
  (analyticMomentInterval2597 13 3).Mem
    (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 13 3)
```

The 2664 generator emitted the 951-module chain and the dry replay reported
`950/950 byte-stable; umbrella stable: True`. The exact ledger passes both
axes, with real and imaginary margins approximately `2401.5671` and
`2391.3427` times their scaled charges. This is the frozen-edge,
non-`psi_zero` branch.

The first umbrella build exposed a Lean 4.30 simplifier failure in the
generated P148 bridge (`unknown free variable HSub`) for a very large rational
residual. The generator now uses the definitionally equal `exact h` bridge
for entry-scoped modules, leaving the legacy lane byte-stable. The regenerated
chain passed the same dry replay, and the P148 module was independently
rechecked with the standard axiom trio.

The Linux-native Lean 4.30 umbrella build completed `4691/4691` jobs. The
assembly build completed `4886/4886` jobs. The final assembly census has 1856
axiom records, including 115 fresh and 1741 replayed records, all exactly
`[propext, Classical.choice, Quot.sound]`. It reports zero errors, zero
`sorryAx`, zero `uses sorry`, 15/15 new module oleans, and 965/965
entry-directory oleans.

The assembly digest is
`4a79cba5c81a150bada94495b673cd50774e6353af7458c58b9952438d068df7`.
The refreshed manifest contains 49 disk-verified parameterized entries, with
chain digest
`fba619236f21c222a8561d1c47042b85b0bcc6a198723ab2f05dd874d610b88b` for this
entry.

This closes one analytic matrix-entry premise for the 2596/2601 owner
interface. It does not close the remaining parameterized off-diagonal entries,
the static defect consumer, the actual defect-operator identity, the
selected-detector signed C3' budget, `chargeRest`, the signed infinite tail,
Producer GO, `SourceRH`, or RH. The hand-written `(0,3)` membership and the
repaired-owner cell certificates remain separate evidence routes.

Evidence:

- `scripts/gen_2664_entry.py`
- `scripts/gen_2663_assembly.py`
- `scripts/gen_2663_panels.py`
- `results/2664_budget_recon_13_3.json`
- `results/2664_assembly_13_3.json`
- `results/2664_offdiag_manifest.json`
- `ConnesWeilRH/Dev/OffDiagE13_03/C1RouteAEntryAssembly2663.lean`
