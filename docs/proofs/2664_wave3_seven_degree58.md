Record 2664 wave 3: the degree-58 ladder subgroup closes -- seven entries
certified, ladder render path validated under the fixed renderer
Date: 2026-10-11

Result

Positive.  Seven new off-diagonal memberships are GREEN end to end, all at
degree 58 in the bars-ladder (non-psi) lane: (17,3), (18,3), (23,2), (24,2),
(25,2), (26,2) and (27,2).  Each proves its membership theorem

    theorem entry{RRCC}Mem2663 :
        (analyticMomentInterval2597 R C).Mem
          (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 R C)

in its rendered `OffDiagE{RR}_{CC}/C1RouteAEntryAssembly2663.lean`, with
every audited leaf on exactly [propext, Classical.choice, Quot.sound], no
sorryAx, 0 errors and 0 uses-sorry across all 14 builds (7 umbrella + 7
assembly), 15/15 census gates and 965 entry oleans per entry.  This wave
CLOSES the degree-58 rung of the survey ladder (7/7 members) and is the
first degree-58 build set under the fixed chain renderer -- wave-1's (29,3)
at degree 66 predates the verbatim-spelling fix, so the ladder path is now
validated end to end post-fix.  No producer, SourceRH, or RH claim is made
or implied.

1. The wave and the candidate ranking

   The committed ladder plan (record 2664 psi=0 batch, section 7) escalates
   the polynomial degree for the survey members whose degree-55 boxes fail:
   rungs 58, 60, 63, 66, 70.  Wave 3 is the COMPLETE degree-58 subgroup --
   seven survey members with first_pass_degree=58, each reading r55
   inside=False and r58 inside=True in the committed summary
   (results/2664_offdiag_survey_summary.json).  Ranking: risk-ascending
   build order (smallest row first; the fail-fast driver makes (17,3) the
   de facto pilot), with (27,2) placed LAST as the subgroup's thin-margin
   adjudication case (survey min margin over box 0.035062, the thinnest
   reading in the entire ladder).

2. Prep (Windows side, _probe/batch_wave3_prep_2664.py)

   Wave-2 prep clone with per-entry degree support (ENTRIES now carry
   (row, col, degree); the emit and dry steps pass --degree=58, and the
   survey cross-check asserts first_pass_degree == 58 AND the rung AT 58
   reads inside=True -- the wave-2 clone defaulted to degree 55 and would
   have failed recon for exactly this subgroup).  The non-psi inverse gate
   (entryPhaseCancel2663 / entryImEqZero2663 absent from the Assembly
   module) and the frozen/general token hygiene are retained unchanged.

   All seven: emit 950 modules + umbrella, dry 950/950 byte-stable,
   recon passes=True (frozen branch throughout -- betas 2.1632/2.6912 sit
   below the 51923/10000 banner), asm OK (15 modules, committed artifacts
   only), hygiene OK (7 checks, frozen).  WAVE3-PREP-OK with the summary
   block on disk (_probe/wave3_prep_log.txt).

3. Build (WSL, _probe/batch_wave3_build_2664.sh)

   Driver 2026-10-11T03:37:02Z (first sync) -> BATCH-DONE after the last
   ENTRY-DONE at 04:29:44Z: 52 min 42 s for 7 fresh entries, strictly
   sequential (two-sided md5 sync, umbrella stage heavy class 4691-job
   plan, assembly stage normal class 4886-job plan, census).  The same
   two plan sizes as wave 2 -- degree changes content, not module counts.

   +-------+------------+---------+---------+---------------+------------------+------------------+
   | entry | beta       | branch  | survey  | recon ratio   | chain digest     | assembly digest  |
   |       |            |         | margin  | (re/im)       | (16-hex prefix)  | (16-hex prefix)  |
   +-------+------------+---------+---------+---------------+------------------+------------------+
   | (17,3) | 2.6912000 | frozen  | 35.2146 | 738.0 / 730.8 | b3e01cefcc11a29a | fc94c6be56c8e54e |
   | (18,3) | 2.6912000 | frozen  | 41.7758 | 952.3 / 953.1 | ebf86c6fb4c4545f | b8b3eb32f6881059 |
   | (23,2) | 2.1632000 | frozen  | 446.6964 | 7250.8 / 7212.8 | de79646a19511340 | 50c8537b8fa472a3 |
   | (24,2) | 2.1632000 | frozen  | 142.0734 | 2580.1 / 2578.0 | d937ff497d199d7f | 39d09bf201924da6 |
   | (25,2) | 2.1632000 | frozen  | 44.0907 | 913.8 / 914.9 | 13edcc0b72b946ac | 357fb9e6e5f4cb78 |
   | (26,2) | 2.1632000 | frozen  | 45.2081 | 1047.3 / 1048.9 | 8f0a349ccf6f4334 | 9b2fde0bdedd57cb |
   | (27,2) | 2.1632000 | frozen  | 0.0351 | 27.7 / 27.5 | a95cc162c309b1a9 | eacd865bed01b775 |
   +-------+------------+---------+---------+---------------+------------------+------------------+

   (survey margin = deg-58 min margin over box from the summary artifact;
   recon ratio = certified margin / total scaled charge from the recon
   payload, both coordinates; betas exact in results/2664_budget_recon_*.json
   -- 2.6912 and 2.1632 exactly.)

   Walls: umbrella 356-411 s per entry, assembly 33-35 s.  Per entry the
   driver log attests footer=1 on both stages, 0 error lines, 0 uses-sorry,
   0 sorryAx, 965 oleans, 15/15 census gates, and the identical axiom
   footprint 1856 records = 115 fresh + 1741 cached replays, 0 nonstandard.

4. Evidence and consistency signatures

   Per entry: results/2664_assembly_{R}_{C}.json (two-sided byte equality,
   footer, zero errors/uses-sorry/sorryAx, exact axiom trio, 15 new module
   oleans, 965 entry oleans, membership shape, member-record trio) and
   results/2664_build_{R}_{C}.json (driver-attested plus whole-log
   reconciliation, sizes, warning breakdown).  Chains disk-verified in
   results/2664_offdiag_manifest.json, now 30 entries (the 14 psi=0, the
   degree-66 (29,3), wave 2's eight, these seven; the hand-written (0,3)
   lane lives in the 2663 record and is not a manifest row).

   Footprint signature: all SEVEN entries read fresh_total=115 /
   chain_replay=1741 (1856 records) -- identical to wave 2, so the
   footprint is DEGREE-INDEPENDENT as well as branch-independent for
   non-psi entries (the psi=0 entries' 117 fresh carries exactly the two
   insert lemmas).  Tree sizes 166.5-169.6 MB of sources / 848-853 MB of
   oleans per entry (~7.1 GB total) at 965 .lean files each.

   Warning accounting (same shape as wave 2): umbrella logs carry 80
   warning lines = 3 Lake package local-changes notices + 77 pre-existing
   ConnesWeilRH/Source warnings + 0 entry-path lines; the assembly-stage
   census gate entry_warnings_only_known_show=True on all seven (the one
   inherited Tiling:277 style.show).

5. Adjudications and preemptions

   (a) (27,2), the thin-margin case: RESOLVED AT 58.  The survey's float
       min margin over box 0.035062 (thinnest in the ladder) is a screen;
       the recon gate recomputes the exact rational barriers from the
       rendered degree-58 chain and reads passes=True with certified margin
       ratio 27.7 / 27.5.  Together with wave-2's (16,3) (1.1543 -> 33.9),
       the pattern is now measured twice: thin box-screen margins open by
       ~25-1000x under exact recomputation, so the screen decides ORDER,
       the recon decides DEGREE.

   (b) Preemption (tooling, applied): the build-evidence assembler
       (_probe/assemble_2664_build_evidence.py) carried the CONSTANT
       degree label 55 -- correct for every prior user (all degree 55;
       (29,3)'s payload predates this assembler) and wrong for the first
       degree-58 wave.  This is erratum 2's class applied to the degree
       field, preempted BEFORE use: the assembler now derives the label
       from the entry payload (results/2664_entry_{TAG}.json, the same
       source the census assembler follows), and a scratch regression
       control (OUT redirected to a temp path) re-ran tag (22,2) and
       reproduced its committed payload BYTE-IDENTICALLY (3313 bytes),
       proving the patch inert for wave-2 while fixing wave-3.  The psi=0
       and wave-2 build payloads remain byte-frozen (never re-run).

6. Provenance

   All seven chains carry the FIXED chain-renderer hash
   gen_2664_entry.py = c3199d0c107c1c8e... (identical to wave 2; no
   generator-hash lag).  Each entry was byte-gated by its own dry pass
   (950/950) before the build.  The manifest refresh resolves to 30
   entries, all disk_verified.

   Disk state: the seven wave trees measure ~7.1 GB against ~207 GB free
   on the WSL volume after the wave; the plan's between-wave deletion
   remains DEFERRED (no pressure), to be re-evaluated before a later wave.

7. Scope and next

   Class accounting after wave 3: the non-psi ladder stands at 8 of 22
   built -- the 66 rung ((29,3), wave 1) and the complete 58 rung (these
   seven); 14 remain (60: 8, 63: 6; the 70 rung is unused, and the ">70"
   histogram bucket is exactly the 14 psi=0 members, replaced by the
   exact-zero route).  The degree-55 class stands at 9 of 834 built
   ((0,3) and wave 2's eight); 825 remain.  Total off-diagonal memberships
   landed: 31 of 870.  Next per the committed plan: continue the wave
   protocol -- the degree-60 subgroup is the natural next ladder slice
   (8 members), interleaved with degree-55 waves -- with per-wave byte
   re-verification and manifest refresh.  This record closes wave 3 only:
   no entry partition sum beyond one entry, no producer margin, no
   SourceRH, no RH claim.
