# Record 2705: off-diagonal entry (11,9) membership

Status: ENTRY MEMBERSHIP GREEN; MANIFEST-FACADE REBUILD PENDING.

The degree-55 exact ledger for entry `(11,9)` passes all four real/imaginary
rectangle barriers. The total scaled charge is about `2.204172e-70`; the
real and imaginary margin-to-charge ratios are about `385346.6` and
`391070.9`.

The 950-module chain regenerated from the committed capture and generators,
and the dry run was byte-stable at 950/950. Linux-native Lean 4.30 built the
umbrella in 4691 Lake jobs and the assembly in 4886 jobs. The membership
theorem is `entry1109Mem2663`. Its assembly census contains 1856 axiom records,
all exactly `[propext, Classical.choice, Quot.sound]`, with zero errors,
`sorryAx`, or uses of `sorry`; all 965 entry oleans are present and the two
source copies agree byte-for-byte.

The committed off-diagonal manifest now has 51 disk-verified entry chains.
With the separate `(0,3)` theorem, 52 of 870 off-diagonal memberships are
wired and 818 remain. The updated manifest facade and 2695 consumer have not
yet been rebuilt after importing `(11,9)`. This entry does not establish
analytic interval soundness for all matrix entries, the actual-owner identity,
the C3' producer margin, `SourceRH`, or RH.

Evidence:

- `results/2664_budget_recon_11_9.json`
- `results/2664_bars_11_9.json`
- `results/2664_assembly_11_9.json`
- `results/2664_offdiag_manifest.json`
- `ConnesWeilRH/Dev/OffDiagE11_09/C1RouteAEntryAssembly2663.lean`
