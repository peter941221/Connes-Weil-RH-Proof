# Record 2703: entry (0,2) analytic membership

Status: GREEN ENTRY MEMBERSHIP; NO PRODUCER OR RH CLAIM.

The degree-55 record-2664 chain for matrix entry `(0,2)` was regenerated from
the committed capture and generators. The exact rational ledger passed all four
coordinate barriers. Its scaled charge is about `8.381242e-70`; the real and
imaginary margins are about 2104.85 and 2090.74 times that charge.

The 950-panel umbrella and the assembly were compiled under Linux-native Lean
4.30 with the resource-aware exclusive build lease. The umbrella completed
4691 Lake jobs. The assembly completed 4886 Lake jobs and proves
`entry0002Mem2663`:

    (analyticMomentInterval2597 0 2).Mem
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 2)

The axiom readback contains only `[propext, Classical.choice, Quot.sound]`;
there is no `sorryAx`, `uses sorry`, or compiler error in the final log.

This closes one of the 820 off-diagonal premises left after the 2664 manifest
and `(0,3)` entry. It does not prove the 2338 analytic coefficient-owner
interval premise, the 2600 aggregate consumer, Producer GO, `SourceRH`, or RH.

Evidence:

- `results/2664_budget_recon_0_2.json`
- `results/2664_bars_0_2.json`
- `results/2664_assembly_0_2.json`
- regenerated chain payload `results/2664_entry_0_2.json` (ignored by design)
- Linux build logs are local verification evidence and are not public artifacts.

Next target: keep entry expansion narrow and prove the actual captured-owner
interval soundness before expanding more cells or claiming a producer result.
