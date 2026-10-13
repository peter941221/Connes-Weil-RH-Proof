# Record 2692 - off-diagonal owner entry (27,7) membership

Status: FORMAL ENTRY MEMBERSHIP GREEN; 47 PARAMETERIZED OFF-DIAGONAL ENTRIES.

The degree-55 nonzero-phase entry `(27,7)` is certified against the analytic
interval table:

```text
entry2707Mem2663 :
  (analyticMomentInterval2597 27 7).Mem
    (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 27 7)
```

The 2664 entry generator emitted the 951-module chain and its dry replay
reported `950/950 byte-stable; umbrella stable: True`. The exact reconstruction
ledger passes both axes: the real and imaginary margins are approximately
`1267.2189` and `1267.5389` times their scaled charges. This is the frozen-edge,
non-`psi_zero` branch.

The first assembly invocation was rejected before compilation because the
15-module assembly half had not yet been rendered; it reported only
`no such file or directory` for `C1RouteAEntryAssembly2663.lean`. After running
the committed `gen_2663_assembly.py --row=27 --col=7` renderer and rechecking the
source sync, the Linux-native Lean 4.30 umbrella build completed `4691/4691`
jobs and the assembly build completed `4886/4886` jobs.

The final assembly census has 1856 axiom records, including 115 fresh and 1741
replayed records; all use exactly `[propext, Classical.choice, Quot.sound]`.
It reports zero errors, zero `sorryAx`, zero `uses sorry`, 15/15 new module
oleans, and 965/965 entry-directory oleans. The assembly digest is
`50e10573519027ea2ab54c7df1e7eeb0d5be4a5893fe594ba95e4a09cd7be05a`.
The refreshed manifest contains 47 disk-verified parameterized entries, with
chain digest
`09c4955fc7bf9f6aa33d6be5620f09a5c6dff5a9baa8b887ea96b99b41649d05` for this
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
- `results/2664_budget_recon_27_7.json`
- `results/2664_assembly_27_7.json`
- `results/2664_offdiag_manifest.json`
- `ConnesWeilRH/Dev/OffDiagE27_07/C1RouteAEntryAssembly2663.lean`
