# Record 2690 - off-diagonal owner entry (1,3) membership

Status: FORMAL ENTRY MEMBERSHIP GREEN; ONE OF 870 OFF-DIAGONAL ENTRIES.

The degree-55 phase-carrying entry `(1,3)` is certified against the analytic
interval table:

```text
entry0103Mem2663 :
  (analyticMomentInterval2597 1 3).Mem
    (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 1 3)
```

The 2664 generator emitted the 951-module chain and 15-module assembly. The
recon ledger passes both axes with margins 513.8183 and 515.0583 times the
scaled charge. Linux-native Lean 4.30 builds completed 4691 umbrella jobs and
4886 assembly jobs. Source sync is byte-identical, the dry run reports
`950/950 byte-stable`, and the assembly census reports 965/965 oleans.

The assembly audit has 1856 axiom records (115 fresh plus 1741 replay), all
exactly `[propext, Classical.choice, Quot.sound]`; errors, `sorryAx`, and
`uses sorry` are zero. The refreshed off-diagonal manifest has 45 verified
entries, including `(1,3)` with chain digest
`9bf0e54ecf6e7c6c43c8c0ddaef69b2cc5e563d6267111b1a0cd38970e17c4cf` and
assembly digest `817be0230def508f0275adabe469d5ab9013fbb7d11be6872c94d1769daf498a`.

This closes one analytic matrix-entry premise for the 2596/2601 owner
interface. It does not close the remaining 825 degree-55 members, the other
off-diagonal entries, the static defect consumer, the actual defect-operator
identity, the selected-detector signed C3' budget, `chargeRest`, the signed
infinite tail, Producer GO, `SourceRH`, or RH. The repaired-owner cell
certificates remain a separate numerical route.

Evidence:

- `scripts/gen_2664_entry.py`
- `scripts/gen_2663_assembly.py`
- `results/2664_budget_recon_1_3.json`
- `results/2664_assembly_1_3.json`
- `results/2664_offdiag_manifest.json`
- `ConnesWeilRH/Dev/OffDiagE01_03/C1RouteAEntryAssembly2663.lean`
