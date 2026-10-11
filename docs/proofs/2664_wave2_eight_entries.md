Record 2664 wave 2: the degree-55 class opens the rows 13-29 stress band --
eight non-psi entries certified, first general-branch bars-ladder cell
Date: 2026-10-11

Result

Positive.  Eight new off-diagonal memberships are GREEN end to end, all at
degree 55 in the bars-ladder (non-psi) lane: (22,2), (15,3), (29,7), (21,2),
(14,3), (28,7), (4,3) and (16,3).  Each proves its membership theorem

    theorem entry{RRCC}Mem2663 :
        (analyticMomentInterval2597 R C).Mem
          (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 R C)

in its rendered
`OffDiagE{RR}_{CC}/C1RouteAEntryAssembly2663.lean`, with every audited leaf
on exactly [propext, Classical.choice, Quot.sound], no sorryAx, 0 errors and
0 uses-sorry across all 16 builds (8 umbrella + 8 assembly), 15/15 census
gates and 965 entry oleans per entry.  Three firsts: the first GENERAL-branch
entry in the bars-ladder lane ((4,3), beta 7.777568), the first coverage of
the previously unbuilt rows 13-29 band, and the (16,3) thin-margin
adjudication case resolved AT degree 55 (no ladder rung needed).  No
producer, SourceRH, or RH claim is made or implied.

1. The wave and the candidate ranking

   The committed wave protocol (record 2664 psi=0 batch, section 7) walks
   the survey's 833-member degree-55 non-psi class in slices.  Wave 2 is the
   degree-55 STRESS slice: the worst-margin members that also cover the
   not-yet-built row band 13-29 at the dominating columns 2/3/7
   (abs_psi ~ 413-444), plus the (4,3) row-swap control at column 3 (the
   template column, the cheapest swap surface).  Ranking source: the
   committed survey summary (results/2664_offdiag_survey_summary.json,
   deg55_min_margin_over_box_float; formula min_margin_over_box =
   min(slack_lo, slack_hi) / box from scripts/survey_offdiag_2664.py).

   (16,3) was placed LAST deliberately: its survey margin 1.1543 sits below
   the 4x floor, so it is the 55-vs-58 adjudication case -- the prep's recon
   gate decides the degree before any chain is built.

2. Prep (Windows side, _probe/batch_wave2_prep_2664.py)

   The psi=0 prep clone ran the same five-step pipeline per entry (emit,
   dry byte-stability, recon, assembly, hygiene) with three additions for a
   non-psi wave: (a) a survey crossing check -- every planned entry must
   read psi_zero=False and first_pass_degree=55 in the summary artifact
   BEFORE rendering; (b) a NON-psi inverse gate -- the psi=0 insert theorems
   entryPhaseCancel2663 / entryImEqZero2663 must be ABSENT from the rendered
   Assembly module (their presence would be a silent branch-selection
   defect); (c) the frozen-vs-general token hygiene inherited from the psi=0
   prep (the frozen-branch Tiling token counts are lane-independent --
   4x "51923 / 10000" measured on psi=0, (29,3) and the new entries alike).

   All eight: dry 950/950 byte-stable; hygiene 7 checks (frozen) or 8
   (general); recon passes=True.  (4,3) is the wave's GENERAL-branch entry
   (beta 7.777568 > banner 51923/10000 = 5.1923; edge banner 4861/625,
   mid 210) -- the first time the general-branch mechanism meets the
   bars-ladder lane.

3. Build (WSL, _probe/batch_wave2_build_2664.sh)

   Driver 2026-10-11T02:02:35Z (first sync) -> BATCH-DONE after the last
   ENTRY-DONE at 03:00:55Z: 58 min 20 s for 8 fresh entries, strictly
   sequential (sync with a two-sided md5 comparison, umbrella stage heavy
   class 4691-job plan, assembly stage normal class 4886-job plan, census).

   +-------+------------+---------+---------+---------------+------------------+------------------+
   | entry | beta       | branch  | survey  | recon ratio   | chain digest     | assembly digest  |
   |       |            |         | margin  | (re/im)       | (16-hex prefix)  | (16-hex prefix)  |
   +-------+------------+---------+---------+---------------+------------------+------------------+
   | (22,2) | 2.1632000 | frozen  |  4.1208 | 71.4 / 71.4   | 0427d9b1c89d0a56 | 49b3f330f012b1e6 |
   | (15,3) | 2.6912000 | frozen  |  7.9153 | 123.3 / 123.2 | ffb63b4cc3b1b268 | 71aa86416a379c7a |
   | (29,7) | 2.6912000 | frozen  | 15.3200 | 215.4 / 215.4 | 4cdf4e65422a5af5 | a77bb4147b63fbc6 |
   | (21,2) | 2.1632000 | frozen  | 15.5540 | 216.0 / 216.0 | b16d569fa7acb15c | 666edc4e70cf59bf |
   | (14,3) | 2.6912000 | frozen  | 27.2326 | 321.7 / 321.2 | 7b032aa744bf0286 | e514109cbe6a92c7 |
   | (28,7) | 2.6912000 | frozen  | 25.1266 | 303.1 / 303.6 | 08ce96849b83b928 | 6a9b88e1b8f98e7d |
   | (4,3)  | 7.7775680 | general | 10.2079 | 153.4 / 153.4 | 64d0cf533457ea17 | 82e5872beef28082 |
   | (16,3) | 2.6912000 | frozen  |  1.1543 | 33.9 / 33.9   | cee204267c8a339f | 5bf7a55ce98676c6 |
   +-------+------------+---------+---------+---------------+------------------+------------------+

   (survey margin = deg55 min margin over box from the summary artifact;
   recon ratio = certified margin / total scaled charge from the recon
   payload, both coordinates; betas exact in results/2664_budget_recon_*.json.)

   Walls: umbrella 340-391 s per entry, assembly 32-38 s.  Per entry the
   driver log attests footer=1, 0 error lines, 0 uses-sorry, 0 sorryAx, 965
   oleans, 15/15 census gates, and the identical axiom footprint
   1856 records = 115 fresh + 1741 cached replays, 0 nonstandard.

4. Evidence and consistency signatures

   Per entry: results/2664_assembly_{R}_{C}.json (census: two-sided byte
   equality, footer, zero errors/uses-sorry/sorryAx, exact axiom trio,
   fresh print-count match, replay cross-build, 15 new module oleans, 965
   entry oleans, membership shape, member-record trio) and
   results/2664_build_{R}_{C}.json (driver-attested plus whole-log
   reconciliation, sizes, warning breakdown).  The chain digests are
   disk-verified in results/2664_offdiag_manifest.json, now 23 entries.

   Cross-entry footprint signature: all EIGHT non-psi entries read
   fresh_total=115 / chain_replay=1741 (1856 records), versus the psi=0
   entries' 117 fresh (the two psi-insert lemmas entryPhaseCancel2663 /
   entryImEqZero2663 account for exactly the +2).  A uniform footprint
   across a wave is a cheap cross-entry consistency check.

   Warning accounting (revised; see erratum 1): umbrella logs carry 80
   warning lines = 3 Lake package local-changes notices + 77 pre-existing
   ConnesWeilRH/Source warnings + 0 entry-path lines; the assembly logs
   re-emit the closure's 3780 warning lines, of which EXACTLY ONE is
   entry-path: the inherited frozen-template Tiling:277 style.show, present
   in all 23 entries.

5. Adjudications and errata

   (a) (16,3), 55-vs-58: RESOLVED AT 55.  The survey's min margin over box
       1.1543 is below the 4x floor but positive; the recon gate recomputed
       the exact rational barriers from the rendered chain and read
       passes=True with certified margin ratio 33.9 (margin / total scaled
       charge) on both coordinates.  Degree 55 stands; no ladder rung.

   (b) Erratum 1 (cross-record, prose only): the psi=0 batch record
       (docs/proofs/2664_psi0_batch_twelve_entries.md, section 5) phrased
       the umbrella warning count as "3 + 76 + 1 entry-path (Tiling
       style.show)".  The committed artifacts read 3 + 77 + 0 for the
       umbrella log on every entry (the psi=0 payload
       results/2664_build_5_6.json and all sibling payloads carry the
       string "77 pre-existing ... 0 entry-path"), and the single inherited
       Tiling:277 style.show lives in the ASSEMBLY-stage log (which
       compiles the 15 assembly modules).  The umbrella log compiles the
       951-module chain only and never carries entry-path warnings.  No
       payload or log is touched; this erratum corrects the prose.

   (c) Erratum 2 (tooling, applied): the build-evidence assembler
       (_probe/assemble_2664_build_evidence.py) carried the CONSTANT
       branch label "psi_zero" and psi-specific purpose prose -- correct
       for every prior user (all psi=0) and wrong for the first non-psi
       wave.  It now derives the label from the recon payload
       (psi_zero -> "psi_zero" / "bars_ladder") and emits branch-aware
       purpose text.  The psi=0 build payloads are byte-frozen (not
       re-run); the eight wave-2 payloads were re-assembled under the fixed
       script and read branch="bars_ladder".

6. Provenance

   All eight chains carry the FIXED chain-renderer hash
   gen_2664_entry.py = c3199d0c107c1c8e... (the psi=0 batch had six
   first-attempt payloads carrying the pre-fix 74f16f8e... hash with a
   recorded lag).  Wave 2 has no generator-hash lag: every payload was
   rendered after the verbatim-spelling fix and byte-gated by its own dry
   pass.  The manifest refresh resolves to 23 entries, all disk_verified.

   Disk state: the eight wave trees measure 151-159 MB of sources and
   826-833 MB of oleans each (~7.8 GB total) against 239 GB free on the WSL
   volume; the plan's between-wave deletion is DEFERRED (no pressure), to
   be re-evaluated before a later wave.

7. Scope and next

   Class accounting (correcting the psi=0-era "23 ladder" phrasing): the
   degree-55 class has 834 members -- 833 besides the hand-written (0,3) --
   of which (0,3) and these eight are done -> 825 remain.  The non-psi
   ladder has 22 members in total (survey histogram 58: 7, 60: 8, 63: 6,
   66: 1), of which (29,3) (degree 66) is built -> 21 remain; the ">70"
   histogram bucket is exactly the 14 psi=0 members, which the exact-zero
   route replaced (no ladder rung is needed for any of them).  Next per the
   committed
   plan: continue the wave protocol over the degree-55 class with per-wave
   byte re-verification and manifest refresh, interleaving ladder waves as
   the class-covering sample requires.  This record closes wave 2 only: no
   entry partition sum beyond one entry, no producer margin, no SourceRH,
   no RH claim.