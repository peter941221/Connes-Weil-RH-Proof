Record 2664: the (0,1) psi=0-branch off-diagonal membership at the parameterized lane
Date: 2026-10-11

Result

Positive.  The owner moment-matrix entry (0,1) -- the pilot member of the
psi=0 branch of the 2664 off-diagonal survey (phase cancels exactly, so
the true entry is real) -- lies in its committed home rectangle, with
every leaf on exactly `[propext, Classical.choice, Quot.sound]`:

    theorem entry0001Mem2663 :
        (analyticMomentInterval2597 0 1).Mem
          (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 1)

(`ConnesWeilRH/Dev/OffDiagE00_01/C1RouteAEntryAssembly2663.lean`, a
rendered module).  This is the first psi=0-branch membership produced by
the entry-parameterized lane, and the first build of the lane's row-0
shape class.  No producer, `SourceRH`, or RH claim is made or implied.

1. The psi=0 branch (structure and routing)

   For these 14 entries psi = (node_im + modulation_col) * width_col^2 = 0
   exactly (payload psi_exact = 0), so the phase factor is 1 and the true
   entry is real.  The real-coordinate ladder of the wave-1 shape cannot
   close such an entry: any interval-modulus charge on a complex quantity
   hits BOTH coordinates, so an im-channel bar can never be driven below
   its own coordinate floor (observed on the wave-1 degree ladder
   58..70).  The branch therefore routes the im channel through the
   record-2618 exact-zero theorem

      momentEntry2351_im_eq_zero_of_phase_cancel2618 :

   (C1RouteAAnalyticMomentNormalization2618.lean): phase cancellation is
   an exact identity, not an enclosure.

   Concretely the rendered assembly emits, in this branch:

   - `entryPhaseCancel2663` : the phase-cancellation hypothesis
     (node.im + modulation = 0) at the concrete entry;
   - `entryImEqZero2663` : the exact-zero corollary for the true entry;
   - the Rect module's two im barriers become 0-based sign facts under
     the SAME names (`rectImLo2663_le2663 : (rectImLo2663 : Real) <= 0`,
     `rectImHi2663_ge2663 : (0 : Real) <= rectImHi2663`), with the im bar
     literals and their compound ties still emitted as exact identities;
   - the membership im clauses splice to
     `le_trans (le_trans (le_of_eq rectImLo2663_tie2663)
     rectImLo2663_le2663) (le_of_eq entryImEqZero2663.symm)` and the
     mirror form; the re clauses are unchanged.

   Entry facts: degree 55; beta_exact = 1141581212515476497715201584266747908094732431
   / 356811923176489970264571492362373784095686656 = 3.19939... <= 51923/10000
   (the frozen banner closes by `rw [hn, hw]; norm_num`); 46 vacuous
   panels, the same set [0..22] + [167..189] as the wave-1 entry.

2. The trailing-index defect in the wave-1 generator (found in this
   entry's prep, fixed, both byte gates re-run)

   The owner application `ownerMomentMatrix2351 capturedModulations2584
   capturedNodes2584 0 3` carries its Fin indices TRAILING the vector
   arguments.  The wave-1 swap list could not reach them directly:
   `capturedNodes2584 0` (row pass, 29 attached sites) matched the
   trailing row index only because it is a textual PREFIX of
   `capturedNodes2584 0 3`, and the trailing column index `3` was never
   swapped at all.  The (29,3) lane was blind to this for two independent
   reasons: col 3 IS the template column, and the row swap fixed the
   trailing row index as a substring side effect.

   For (0,1) the row swap is a no-op (row = 0), so the full-application
   sites would have kept the template column: the first re-emission read
   `... capturedNodes2584 0 3` at 10 sites.  Fix in
   `scripts/gen_2663_assembly.py`: swap the full application FIRST with a
   count-10 assert, which also removes those sites from the attached
   `capturedNodes2584 0` count for row != 0.  The attached-count assert is
   therefore row-aware: 29 when row = 0 (the 10 rewritten sites still
   contain the prefix and map to themselves), 19 when row != 0.
   Completeness gate on the emitted tree: zero stale ` 0 3`,
   `capturedModulations2584 3` or `r3^2` survive; the 10 owner sites read
   `0 1` (12 with the psi=0 insert).  Byte gates after the fix: Gate A
   (legacy (0,3) no-argument re-run) gives zero diff under
   ConnesWeilRH/Dev; Gate B ((29,3) regeneration, --row=29 --col=3)
   reproduces the committed per-module sha256 set exactly, canonical
   digest 5ddc0d70c33c0856707c9e68a193084b1d025278e4d69373f18c24b4b0c93ef9.

3. Byte evidence (committed)

   - `results/2664_assembly_0_1.json`: per-module sha256 for the 15
     assembly modules (staged source vs the mirror copies that were
     built), the canonical
     `assembly_sha256 = 62236601b1b895e102cea037cff9af6276eaa4f4e3e700ea1417062cf42e2398`
     (same canonical-JSON convention as the chain payloads), provenance
     hashes (generator `830c69d2..` = the FIXED generator text, both
     templates `e7fc648b..` / `5b8dd171..`, the (0,1) bars/recon slots
     `e65d9d69..` / `ba8718fe..`), and the build gate table (15/15
     green).
   - `results/2664_offdiag_manifest.json`: (0,1) with
     `disk_verified = true`, `chain_sha256 = 6540025a56f5ef52..` (951
     modules), plus the new `assembly_sha256`/`assembly_modules` fields;
     (29,3) unchanged (`e9ee6e4d2110fcba..`).
   - `results/2664_build_0_1.json`: the staged build settlement
     (umbrella + assembly stages, sizes, smoke-omission note).

4. Build census (read from the logs, not the exit code)

   Stage 1, target `ConnesWeilRH.Dev.C1RouteAOffDiagEntry2664E00_01`,
   heavy class, 4691-job plan, 2026-10-10T22:40:37Z to 22:46:15Z (338 s):
   footer `Build completed successfully`, 0 `error:` lines, 0
   `uses sorry`, 0 `sorryAx`, 965 entry-directory oleans,
   UMBRELLA-OLEAN-OK, 1739 axiom records all exactly
   `[propext, Classical.choice, Quot.sound]`.  Warnings 80 / entry-path
   0: the same 3 Lake package local-changes notices plus the 77
   pre-existing ConnesWeilRH/Source warnings as wave 1; zero warnings on
   the 950 chain modules.

   Stage 2, target `...C1RouteAEntryAssembly2663`, normal class,
   4886-job plan, 31 s: 0 errors, 0 `uses sorry`; the gated census
   (15/15 true, `assembly_sha256` above) reads axiom records 1858 with 0
   nonstandard.  Decomposition: 117 fresh records -- per-file counts
   equal the `#print axioms` site counts, Assembly 22 (wave 1: 20, plus
   exactly the two psi=0 insert theorems `entryPhaseCancel2663` and
   `entryImEqZero2663`), Tiling 23, Rect 12, Bars 5, Panels 5, B00..B09
   5 each -- plus 1741 replayed from the cached closure; 1739 + 2 + 117 =
   1858.  Cross-build anchor: per-file counts are IDENTICAL on all 195
   shared files, no umbrella-only file exists, and the asm-only set is
   exactly the 15 fresh modules plus one closure addition
   (`C1RouteAAdaptiveN05440Minus2542`, 2 records, pulled by the assembly
   imports).

   Instrument notes.  (a) No separate pre-build smoke was run for this
   entry; the two renderer byte gates of section 2 were the pre-build
   control and the umbrella stage was the first compile of this tree
   (including the row-0 shape class).  Documented in the build artifact
   rather than papered over.  (b) Mid-run `[n/N]` windows are not
   verdicts: the plan total GROWS during a heavy run (observed
   3865 -> 4250 -> 4691 on this build, final footer count 4691); judge
   by the footer, the full error list and the olean census.

5. One inherited style warning and the inherited prose tags

   The rendered tiling emits the `style.show` linter warning at
   `C1RouteAEntryTiling2663.lean:277:4`, identical to wave 1; the census
   asserts entry-path warnings are exactly this one line.

   The 950-module chain renderer does not rewrite docstring tokens, so
   the (0,1) tree carries the wave-1 prose: 570 files (190 each of
   AmpPin2657, ComplexPanelTable2655, PhasePin2658) say "entry (0, 3)",
   190 AmpPin files say "column-3 parameters", and the Rect docstring's
   barrier sketch says "`r3sq = widthSq2663`".  All of it is comment
   prose, none of it reaches a term; the (29,3) tree carries the SAME
   tokens with the SAME counts and is green.  Fix deferred to wave prep,
   when the renderers may move without invalidating the Gate B digest.

6. Scope and next

   This pilot validates the psi=0 branch end to end: generator insert
   path, the trailing-index fix, row-0 shape class, build and census.
   The remaining 13 psi=0 entries on this branch are (0,4), (1,0),
   (1,4), (2,3), (3,2), (4,0), (4,1), (5,6), (5,7), (6,5), (6,7),
   (7,5), (7,6); entries with both row != 0 and col != 3 exercise the
   fixed trailing-index path end to end for the first time ((1,4) is the
   first such candidate).  The psi=0 chains are also materially leaner:
   84,048,546 B of sources and 654,946,670 B of oleans against wave-1's
   212,432,808 B / 835,175,837 B, because the degree-55 tables carry
   zero imaginary channels (391 KB per active-panel table against 1.09
   MB for the degree-66 phase-carrying table on the same panel
   P108/P090, a measured 2.79x ratio).

   The wave protocol is unchanged: 833 degree-55 entries, the 23
   ladder entries, and this 14-entry psi=0 branch, built in waves with
   deletion between waves, artifact-level assembly, and per-wave byte
   re-verification against the generators.

   Evidence: `results/2664_assembly_0_1.json`,
   `results/2664_build_0_1.json`, `results/2664_offdiag_manifest.json`,
   the build logs `entry2664_umbrella_0_1.log` /
   `entry2664_asm_build_0_1.log` (on disk, repo-ignored), and the
   drivers `_probe/run_build_e0001_2664.sh`,
   `_probe/assemble_2664_asm_evidence_0_1.py` (local, gitignored).