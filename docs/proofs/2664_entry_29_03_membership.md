Record 2664: the (29,3) off-diagonal membership at the parameterized lane
Date: 2026-10-11

Result

Positive.  The owner moment-matrix entry (29,3) -- the worst-class member
of the 2664 off-diagonal survey (the degree-66 ladder case, psi != 0, the
largest captured node height) -- lies in its committed home rectangle,
with every leaf on exactly `[propext, Classical.choice, Quot.sound]`:

    theorem entry2903Mem2663 :
        (analyticMomentInterval2597 29 3).Mem
          (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 29 3)

(`ConnesWeilRH/Dev/OffDiagE29_03/C1RouteAEntryAssembly2663.lean`, a
rendered module).  This is the first off-diagonal membership produced by
the entry-parameterized lane; the (0,3) lane of records 2661-2663 was
hand-written, and the 30 diagonal entries were closed by record 2644.
No producer, `SourceRH`, or RH claim is made or implied.

1. The entry lane (scope-parameterized rendering)

   One entry = a 950-module chain under `ConnesWeilRH/Dev/OffDiagE{R}_{C}/`
   (5 families x 190 panels: `C1RouteAAmpPin2657`,
   `C1RouteAComplexPanelAnalytic2656`, `C1RouteAComplexPanelTable2655`,
   `C1RouteAPanelTrueBall2662`, `C1RouteAPhasePin2658`) plus the umbrella
   `ConnesWeilRH/Dev/C1RouteAOffDiagEntry2664E{R}_{C}`.  The assembly
   half is 15 further modules rendered by

       python scripts/gen_2663_assembly.py --row=29 --col=3

   from the committed (0,3) texts (`C1RouteAEntryTiling2663`,
   `C1RouteAEntryAssembly2663`) by assert-counted token substitution:
   namespace, the node/modulation/width indices, the node-29 and width-3
   capture literals, the interval-table row `analyticMomentInterval2597
   29 3`, and the membership theorem name.  Every numeric slot is read
   back from committed artifacts (the capture module, the bars/recon
   payloads, and the on-disk `nodeEntry29_2662P000` literal through the
   `gen_2663_slots` wire tie); no float display text enters any module.
   The 51923/10000 beta banner that was load-bearing at node 0 holds
   trivially at node 29: `Re(node29) = 1/2` exactly (capture line 106).

   Legacy byte-stability gate: the no-argument invocation of the
   generator reproduces all 13 committed (0,3) support modules bitwise
   (git status clean across the DEV root after the entry run), so the
   parameterization is behavior-preserving on the home lane.

2. Byte evidence (committed)

   - `results/2664_assembly_29_3.json`: per-module sha256 for the 15
     assembly modules (two-sided byte check, staged source vs the mirror
     copies that were built), the canonical
     `assembly_sha256 = 5ddc0d70c33c0856707c9e68a193084b1d025278e4d69373f18c24b4b0c93ef9`
     (the same canonical-JSON convention as the chain payloads),
     provenance hashes (generator `924e733d..`, both templates, the slot
     payloads), and the build gate table (15/15 green).
   - `results/2664_offdiag_manifest.json`: (29,3) with
     `disk_verified = true`, `chain_sha256 = e9ee6e4d2110fcba..` (951
     modules) plus the new `assembly_sha256`/`assembly_modules` fields.
     `scripts/build_entry_manifest_2664.py` now verifies the assembly
     payload from disk and excludes its modules from the chain-extra
     check; payload-absent control run: exit 1 with exactly the 15
     assembly modules reported as extras (the old strict behavior).

3. Build census (read from the log, not the exit code)

   Target `ConnesWeilRH.Dev.OffDiagE29_03.C1RouteAEntryAssembly2663`,
   normal class, 4886-job plan: footer `Build completed successfully`,
   exactly 15 `Built` lines (the 950 chain oleans were cached; plan
   positions 4872..4886), 0 `error:` lines, 0 `uses sorry`, 0 `sorryAx`,
   965 entry-directory oleans, 15/15 new oleans, umbrella olean present.

   Axiom records: 1856, every bracket exactly `[propext,
   Classical.choice, Quot.sound]`, 0 nonstandard -- including the
   membership record itself (`entry2903Mem2663`).  Decomposition of the
   total: 115 fresh records (the 15 modules; the per-file log counts
   equal the `#print axioms` site counts of the sources) plus 1741
   replayed from the cached closure (lake replays stored diagnostics of
   cached modules).  Cross-build replay anchor: against the wave-1
   umbrella log (1739 records), the per-file counts are IDENTICAL on all
   195 shared files, no umbrella-only file exists, and the asm-only set
   is exactly the 15 fresh modules plus ONE closure addition
   (`C1RouteAAdaptiveN05440Minus2542`, 2 records, pulled by the assembly
   imports): 1739 + 2 + 115 = 1856.

4. One inherited style warning (and a 2663 prose erratum)

   The rendered tiling emits the `style.show` linter warning at
   `C1RouteAEntryTiling2663.lean:277:4`.  It is present in the committed
   (0,3) template (frozen md5 `8f85469c5251d6d1b6c4c61a815ea249`) and in
   the legacy membership log (`results/build_2663_membership_final.log`,
   line 12363).  The render preserves the template line-for-line; the
   census asserts entry-path warnings are exactly this one line.  Erratum
   for the record-2663 part-1 prose "0 errors, 0 warnings" about the
   tiling: the frozen source yields one `style.show` warning, so that
   count should read one style warning.  (Part 2's "two new modules"
   reading stays correct; its fresh set was Panels + Assembly.)

5. Scope and next

   Phase A (committed survey): 870 off-diagonal entries priced; 833 close
   at degree 55 with >= 4x margin, 23 need 58/60/63/66-rung ladders
   ((29,3) is the degree-66 worst), and 14 psi_zero entries need the
   separate pipeline branch.  Disk wall: one chain is 212,432,808 B of
   sources plus 835,175,837 B of oleans; 869 chains would need roughly
   150-190 GB of sources and 600-700 GB of oleans against the available
   disk, so the monolithic Lean batch is infeasible on this machine.
   The scoped plan is a class-covering sample (833 + 23 + 14 classes)
   built in waves with deletion between waves, artifact-level assembly,
   and per-wave byte re-verification against the generators.

   Evidence: `results/2664_assembly_29_3.json`,
   `results/2664_offdiag_manifest.json`, the build log
   `entry2664_asm_build.log` (on disk, repo-ignored), and the driver
   `_probe/run_2664_asm_build.sh` (local, gitignored).