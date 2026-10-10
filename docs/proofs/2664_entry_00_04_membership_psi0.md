Record 2664: the (0,4) psi=0-branch off-diagonal membership -- first
interior-index psi=0 insert and first over-banner edge build
Date: 2026-10-11

Result

Positive.  The owner moment-matrix entry (0,4) -- the batch representative
of the 2664 psi=0 branch, chosen because it is the first psi=0 entry of
the record to leave the frozen banner -- lies in its committed home
rectangle, with every leaf on exactly `[propext, Classical.choice,
Quot.sound]`:

    theorem entry0004Mem2663 :
        (analyticMomentInterval2597 0 4).Mem
          (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 4)

(`ConnesWeilRH/Dev/OffDiagE00_04/C1RouteAEntryAssembly2663.lean`, a
rendered module).  Two firsts over the (0,1) pilot: the psi=0 insert at an
INTERIOR vector index (4), where the pilot's bracket form fails (its col 1
is the one index beyond 0 that Mathlib's VecNotation makes @[simp]); and
the first build of the Tiling's edge-GENERAL branch (beta > frozen
banner).  No producer, `SourceRH`, or RH claim is made or implied.

1. The psi=0 insert at an interior index (the @[simp] cons_val boundary)

   The branch inserts, at the concrete entry, the phase-cancellation
   hypothesis `(capturedNodes2584 row).im + capturedModulations2584 col =
   0` and its exact-zero corollary (record 2618's identity; the (0,1)
   record section 1 states the routing).  The pilot proved the insert by
   `norm_num [capturedNodes2584, capturedModulations2584]`, which closed
   at col 1.

   For (0,4) the first assembly stage failed (driver stage 2,
   2026-10-10T23:23:01Z -> 23:23:28Z, exit 1, footer 0, 3 error lines):
   unsolved goals at `C1RouteAEntryAssembly2663.lean:583:64`, the residue
   reading

       |- 5524291025718029 / 140737488355328 + ![..., -(5524291025718029 /
            140737488355328), 0, 0, 0, ...] 4 = 0

   -- the vector literal stuck at index 4 (the `![...] 4` application
   never reduced).  `entryPhaseCancel2663`, `entryImEqZero2663` and
   `entry0004Mem2663` degraded to sorryAx (3 such records in the failed
   log; log preserved as `entry2664_asm_build_0_4_failed.log` and
   `_probe/asm_fail_0_4_2664.log`).

   Root cause (Mathlib VecNotation, pinned v4.30): `cons_val_zero`,
   `cons_val_succ` and `cons_val_one` are @[simp]; `cons_val_two`,
   `cons_val_three`, `cons_val_four` are plain lemmas, and the
   `dsimproc cons_val` does NOT fire under `norm_num`.  Every literal
   index >= 2 therefore stays unreduced on this route; (0,1) was
   accidentally inside the @[simp] set.

   Fix in `scripts/gen_2663_assembly.py`: emit the insert as a kernel-rfl
   literal pin -- the Tiling's own node/width pattern, valid at any
   literal index 0..29 (the 2be law family):

       have hn : (capturedNodes2584 0).im =
           ((5524291025718029 : Real) / 140737488355328) := rfl
       have hm : capturedModulations2584 4 =
           ((-5524291025718029 : Real) / 140737488355328) := rfl
       rw [hn, hm]
       norm_num

   The two literals are extracted VERBATIM from the capture module
   (`capture_psi_literals_2584`), and the exact-sum invariant
   `node_im + modulation = 0` is asserted from the literals, not from
   floats.  The assembly re-run is green (section 5).

2. The over-banner edge-general branch (first build)

   Entry facts: degree 55; beta_exact =
   8839161902577304865537505944957810006522086239
   / 1427247692705959881058285969449495136382746624 = 6.193152000000003
   > 51923/10000 (the frozen banner).  This is the first entry of the
   record on the Tiling's edge-general branch, selected in recon
   (`results/2664_budget_recon_0_4.json`: `edge_branch = "general"`,
   `passes = true`, `psi_zero = true`), and the first build of that
   branch.

   The general render replaces, with count asserts: the banner literal by
   its 4-decimal CEIL 15483/2500 = 6.1932 (tiling count 4; closes by
   `rw [hn, hw]; norm_num`; exact slack ~4.8e-5), the edge midpoint
   `605/2` by `210` (`-(210)` count 2), and the frozen 302-exponent hbase
   by the `Real.exp_one_gt_d9` chain (count 1):

       have hbar : Real.exp (-(210)) <= 1 / (2 : Real) ^ 302
       ...  hbase : (2 : Real) ^ 302 <= (2718 / 1000 : Real) ^ 210 := by
              norm_num
            he : (2718 / 1000 : Real) <= Real.exp 1 := by
              linarith [Real.exp_one_gt_d9]
            calc (2 : Real) ^ 302 <= (2718 / 1000 : Real) ^ 210 := hbase
              _ <= (Real.exp 1) ^ 210 := pow_le_pow_left0 ... he 210
              _ = Real.exp 210

   plus the scoped `set_option exponentiation.threshold 400 in` wrappers
   (tiling count 5, assembly count 2) so `norm_num` may evaluate the
   302-digit literal power.  Token census on the emitted tree: zero stale
   `51923` survive in the tiling, one banner mention survives in the
   assembly prose with the general value (count 1).  The two im-barrier
   sign facts and the membership splice shape are as in the (0,1) record
   section 1; here the spliced exact-zero closes against the node-0 im
   literal `+5524291025718029/140737488355328` and modulation 4 of the
   same magnitude with opposite sign.

3. The verbatim-spelling law (batch-prep findings on (5,6)/(6,5), fixed,
   byte-gated)

   Two batch trees rendered before this entry refused at the generator's
   own membership gate: (5,6) at the width pin (`((2 : Real) / 1)` not in
   the capture module) and (6,5) at the node pin (`((1 : Real) / 1)`).
   Root cause: the capture module spells NON-INTEGER rationals as
   `((n : Real) / d)` but INTEGER-valued slots BARE -- `capturedWidth2584
   6 = (2 : Real)`, `capturedNodes2584 6 = <(1 : Real), (0 : Real)>`.  The
   generator's canonical `((n : Real) / 1)` construction is neither
   present in the source nor admissible at the substitution sites, which
   are kernel-rfl pins against the capture literals (the Tiling's own
   `have hn : ... := rfl` / `have hw : storedWidth c = ... := by rw
   [storedWidth_eq_capturedWidth2584]; rfl` pattern): only the capture's
   own spelling may be substituted.

   Fix in `scripts/gen_2663_assembly.py`: new `_capture_vectors_2584()`
   extracts all four capture vectors verbatim (paren-depth-aware split);
   the node/width literals are taken from it with exact-value tie asserts
   (`literal_fraction(spell) == expected`), and the batch hygiene check
   gained the two spelling gates (`tiling_node_spell`,
   `tiling_wid_spell`).  (5,6) and (6,5) then re-render RERENDER-OK; the
   final three-entry prep ((6,7), (7,5), (7,6)) closes BATCH-PREP-OK with
   the extended hygiene (banners 3364/625 and 6/1 general, 51923/10000
   frozen).  The first prep run's failure was reported as exit 0 by the
   harness -- the echo-masks-exit-code recurrence; the verdict was read
   from its log.

   Byte-stability gate `_probe/gate_verbatim_spell_2664.py`: re-render
   each landed lane through the CURRENT generator and require 15/15
   assembly-module sha256 unchanged.  Result GATE-OK on ten lanes
   (legacy (0,3) no-argument zero-diff; (0,4), (29,3), and the eight
   non-psi lanes rendered before the psi fix); both recorded digests
   reproduce -- (0,4) `0bff9c93..` and (29,3) `5ddc0d70..`.  The (0,1)
   lane is EXCLUDED BY DESIGN (documented in the gate): it was rendered
   and built in the superseded bracket era (section 1), so the fixed
   generator legitimately rewrites its insert and re-rendering would
   clobber its committed bytes.  The first gate draft did not exclude it;
   the drifted Windows tree was restored from the census-verified WSL
   mirror copy and verified against the committed artifact
   (`C1RouteAEntryAssembly2663.lean` sha256 = `35461cfa1821174299...` ==
   `results/2664_assembly_0_1.json`'s recorded module hash) before the
   lane was excluded.  Consequence recorded here: the (0,4) assembly
   artifact's provenance holds the psi-fix generator hash
   (`39847ec2..`); the live verbatim-fix generator (`fb584b91..`) differs
   textually but reproduces this entry's 15 modules byte-for-byte per
   the gate, so the byte binding stands.

4. Byte evidence (committed)

   - `results/2664_assembly_0_4.json`: per-module sha256 for the 15
     assembly modules (staged source vs the mirror copies that were
     built, two-sided byte equality true), the canonical
     `assembly_sha256 = 0bff9c933e5a11c16dd8fc6c1d0b3a953554347d6e17561dc319f5193ca4a64e`,
     provenance hashes (generator `39847ec2..`, tiling template
     `e7fc648b..`, assembly template `5b8dd171..`, (0,4) bars/recon slots
     `cf685a66..` / `47903c25..`), and the gate table -- all 15 true:
     footer/zero-errors/zero-uses-sorry/zero-sorryAx, axioms exact trio,
     membership shape, member-record trio, 15 new module oleans,
     965 entry oleans, entry warnings only the known `show` line, fresh
     print counts match, replay shared per-file identical, replay
     umbrella-only empty, replay asm-only expected.
   - `results/2664_build_0_4.json`: the staged build settlement (umbrella
     + assembly re-run + the preserved failed stage, sizes, smoke-omission
     note).
   - `results/2664_offdiag_manifest.json`: unchanged this commit --
     (0,1) and (29,3) only.  The manifest's strict extras check refuses
     while the sibling psi=0 trees sit on disk without assembly payloads
     by design; the (0,4) refresh rides the wave.  Recorded in the build
     artifact's `byte_binding` note.

5. Build census (read from the logs, not the exit code)

   Stage 1, target `ConnesWeilRH.Dev.C1RouteAOffDiagEntry2664E00_04`,
   heavy class, 4691-job plan, 2026-10-10T23:17:44Z to 23:23:01Z (317 s):
   footer `Build completed successfully`, 0 `error:` lines, 0
   `uses sorry`, 0 `sorryAx`, 965 entry-directory oleans,
   UMBRELLA-OLEAN-OK, 1739 axiom records all exactly
   `[propext, Classical.choice, Quot.sound]`.  Warnings 80 / entry-path
   0: the same 3 Lake package local-changes notices plus the 77
   pre-existing ConnesWeilRH/Source warnings as wave 1 and (0,1); zero
   warnings on the 950 chain modules.

   Stage 2 (first attempt): exit 1, footer 0, 3 error lines, 3 sorryAx
   records -- section 1; adjudicated, fixed in the generator, re-run.

   Stage 2 (re-run), target `...C1RouteAEntryAssembly2663`, normal class,
   4886-job plan, 2026-10-10T23:32:46Z to 23:34:12Z (86 s): 0 errors,
   0 `uses sorry`, 0 `sorryAx`; the gated census reads axiom records
   1858 with 0 nonstandard.  Decomposition: 117 fresh records --
   per-file counts equal the `#print axioms` site counts, Assembly 22
   ((0,1): 20, plus exactly the two psi=0 insert theorems), Tiling 23,
   Rect 12, Bars 5, Panels 5, B00..B09 5 each -- plus 1741 replayed from
   the cached closure; 1739 + 2 + 117 = 1858.  Cross-build anchor:
   per-file counts IDENTICAL on all shared files, no umbrella-only file,
   asm-only set exactly the 15 fresh modules plus one closure addition
   (`C1RouteAAdaptiveN05440Minus2542`, pulled by the assembly imports).
   Sizes: 84,849,592 B of sources (965 .lean) and 608,735,208 B of oleans
   (965 .olean) -- the psi=0 lean profile, same class as (0,1).

   Instrument notes.  (a) No separate pre-build smoke was run; the
   generator byte gates (legacy zero-diff, (29,3) digest, verbatim-spell
   gate) were the pre-build control and the umbrella stage was the first
   compile of this tree, including the edge-general branch build.
   Documented in the build artifact.  (b) Mid-run `[n/N]` windows are not
   verdicts (the plan total grows during a heavy run); judge by the
   footer, the full error list and the olean census.  (c) The failed
   stage is preserved as evidence, not deleted: expected-failure controls
   are not production certificates, and the fix was verified by re-run,
   not by re-reading the failure.

6. One inherited style warning and the inherited prose tags

   The rendered tiling emits the `style.show` linter warning at
   `C1RouteAEntryTiling2663.lean:284:4` (line 277 on (0,1); the general
   branch render is longer), identical class to wave 1; the census
   asserts entry-path warnings are exactly this one line.

   The 950-module chain renderer does not rewrite docstring tokens, so
   the (0,4) tree carries the wave-1 prose with the same counts as (0,1):
   570 files (190 each of AmpPin2657, ComplexPanelTable2655, PhasePin2658)
   say "entry (0, 3)", 190 AmpPin files say "column-3 parameters", and
   the Rect docstring's barrier sketch says "`r3sq = widthSq2663`".  All
   of it is comment prose, none of it reaches a term; the (29,3) tree
   carries the SAME tokens with the SAME counts and is green.  Fix
   deferred to wave prep, when the renderers may move without
   invalidating the Gate B digest.

7. Scope and next

   This representative closes the psi=0 batch's mechanism questions end
   to end: the kernel-rfl insert at an arbitrary literal index, the
   over-banner edge-general branch, the verbatim-spelling gate, and the
   build/census protocol at a second psi=0 entry.  The other 12 psi=0
   entries ((1,0), (1,4), (2,3), (3,2), (4,0), (4,1), (5,6), (5,7),
   (6,5), (6,7), (7,5), (7,6)) are fully prepped on the Windows side
   under the CURRENT (verbatim-fix) generator, with three of them on the
   general branch ((6,7) banner 3364/625, (7,6) banner 6/1, plus this
   entry): next is the WSL sync, per-entry umbrella + assembly builds,
   and the per-entry censuses, then the psi=0 wave record and the
   deferred manifest refresh.  The (1,4) lane is the first entry with
   both row != 0 and col != 3, exercising the fixed trailing-index path
   of the (0,1) record section 2 end to end.

   The wave protocol is unchanged: 833 degree-55 entries, the 23 ladder
   entries, and the 14-entry psi=0 branch (1 landed + 13), built in waves
   with deletion between waves, artifact-level assembly, and per-wave
   byte re-verification against the generators.

   Evidence: `results/2664_assembly_0_4.json`,
   `results/2664_build_0_4.json`, `results/2664_budget_recon_0_4.json`,
   `results/2664_entry_0_4.json` (untracked payload with the 951 chain
   module hashes), the build logs `entry2664_umbrella_0_4.log` /
   `entry2664_asm_build_0_4.log` / `entry2664_asm_build_0_4_failed.log`
   (on disk, repo-ignored), and the drivers
   `_probe/gate_verbatim_spell_2664.py`,
   `_probe/batch_psi0_prep_2664.py`,
   `_probe/assemble_2664_build_evidence.py` (local, gitignored).