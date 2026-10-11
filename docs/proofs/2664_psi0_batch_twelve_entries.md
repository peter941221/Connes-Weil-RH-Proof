Record 2664: the psi=0 branch closed -- twelve-entry batch certified,
chain-renderer verbatim-spelling incident and fix
Date: 2026-10-11

Result

Positive.  The twelve-entry psi=0 batch is GREEN end to end, and with it
ALL fourteen psi=0 off-diagonal entries of the record-2664 campaign (the
survey class `psi_zero_offdiag`, `results/2664_offdiag_survey_summary.json`)
are certified: the (0,1) pilot, the (0,4) representative, and the twelve
batch entries (1,0), (1,4), (2,3), (3,2), (4,0), (4,1), (5,6), (5,7),
(6,5), (6,7), (7,5), (7,6).  Each batch entry proves its membership theorem

    theorem entry{RRCC}Mem2663 :
        (analyticMomentInterval2597 R C).Mem
          (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 R C)

in its rendered `OffDiagE{RR}_{CC}/C1RouteAEntryAssembly2663.lean`, with
every audited leaf on exactly `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`, 0 errors and 0 `uses sorry` across all 24 builds (12 umbrella +
12 assembly), and 15/15 census gates per entry.  The batch also produced the
record's second and third edge-GENERAL branch builds ((6,7) and (7,6)).
No producer, `SourceRH`, or RH claim is made or implied.

1. The batch and the branch criterion

   The psi=0 criterion is exact phase cancellation: with
   `psi = (node_im(row) + modulation(col)) * width(col)^2`, the fourteen
   class members have `node_im + modulation = 0` exactly, so the phase
   factor of the entry integrand is identically 1 and the entry's true value
   is real.  The assembly routes the im channel through the record-2618
   exact-zero theorem instead of the bars ladder: a modulus charge hits both
   coordinates, so an exactly-zero im channel can never close an im bar by
   degree (the survey histogram accordingly shows `first_pass_degree` null /
   ">70" for exactly these fourteen).

   Predecessor increments: the (0,1) pilot (bracket-form insert; col 1 is
   the one index beyond 0 inside Mathlib's `@[simp]` cons_val set) and the
   (0,4) representative (insert at an INTERIOR vector index via kernel-rfl
   literal pins; first over-banner build).  The twelve consume both fixes
   unchanged; ten build the frozen-branch edge pins and two cross the banner
   `51923/10000 = 5.1923` and build the edge-GENERAL branch:

       +-------+-----------+---------------+
       | entry | beta      | edge branch   |
       +-------+-----------+---------------+
       | (1,0) | 0.140800  | frozen        |
       | (1,4) | 0.360448  | frozen        |
       | (2,3) | 5.086368  | frozen        |
       | (3,2) | 0.237952  | frozen        |
       | (4,0) | 3.699200  | frozen        |
       | (4,1) | 4.892192  | frozen        |
       | (5,6) | 2.000000  | frozen        |
       | (5,7) | 2.691200  | frozen        |
       | (6,5) | 2.822400  | frozen        |
       | (6,7) | 5.382400  | general       |
       | (7,5) | 4.233600  | frozen        |
       | (7,6) | 6.000000  | general       |
       +-------+-----------+---------------+

   (exact beta strings per entry in `results/2664_assembly_*.json` and the
   manifest; the two general-branch builds reuse the (0,4) over-banner
   mechanism -- 4-decimal ceil banner, `Real.exp_one_gt_d9` hbase chain,
   scoped `exponentiation.threshold 400` wrappers.)

2. First attempt and the stop at (5,6)

   The batch driver (`_probe/batch_psi0_build_2664.sh`, resumable,
   fail-fast) certified six entries in a row (driver-attested stage logs
   2026-10-11T00:00:12Z through 00:43:05Z) and then stopped at (5,6):

       stage1 START=2026-10-11T00:38:39Z END=2026-10-11T00:43:05Z EXIT=1
       stage1 footer: 0
       stage1 errors: 571
       STAGE-FAIL 5_6 umbrella
       BATCH-STOP at 5_6

   (preserved driver-attested log:
   `_probe/batch_psi0_first_attempt_5_6_umbrella_fail.log`.)  The umbrella
   log itself (WSL and the `_probe` copy) was OVERWRITTEN by the green
   relaunch of the same path; the preserved driver log plus the scratch
   reproduction of section 4 are the retained evidence, recorded explicitly
   here rather than reconstructed.

   The failing declaration shape (read before the overwrite) was the
   trueball family's kernel-rfl node pin in ~190 modules,
   `capturedNodes2584_row05_eq2662P000 ... := rfl`, with the compiler's
   "Not a definitional equality" at the theorem line and "Type mismatch" at
   the `rfl` line: the rendered node def carried the canonical
   double-wrapped division spelling `((0 : ℝ) / 1)` while the capture
   module spells the same integer-valued component BARE, `(0 : ℝ)`.

3. Root cause and fix (chain-side verbatim-spelling law)

   The capture (`C1RouteACorrectionCaptureParameters2584.lean`) spells
   non-integer rationals `((n : ℝ) / d)` but integer-valued slots bare:
   `capturedNodes2584` rows 5/6/7 are `⟨((1 : ℝ) / 2), (0 : ℝ)⟩`,
   `⟨(1 : ℝ), (0 : ℝ)⟩`, `⟨((3 : ℝ) / 2), (0 : ℝ)⟩`.  The ASSEMBLY-half
   renderer already extracted these verbatim (the (0,4) fix); the CHAIN
   renderer `scripts/gen_2664_entry.py` built its node literals through
   `spell(frac) = ((n : ℝ) / d)`, canonical at every row.  For rows 0-4 the
   canonical and capture spellings coincide byte-for-byte on every
   component; rows 5/6/7 diverge in EXACTLY four slots (5.im, 6.re, 6.im,
   7.im) -- precisely the six pending entries' nodes.  A fix in one
   renderer of a shared template does not propagate to the sibling renderer
   that re-substitutes the same sites.

   Fix: `node_elements()` splits the `capturedNodes2584` literal into the
   30 verbatim `⟨re, im⟩` component spellings (bracket-depth split, then
   paren-depth component split), wire-tied to the pricing capture's
   `nodes_hex` floats through `rational_spelling_value`; the trueball ctx
   now receives those literals directly.  Rows 0-4 was proven unaffected
   (canonical spell == verbatim extraction asserted slot by slot against
   the capture) BEFORE any re-render; only the six affected trees were
   re-emitted.

4. Differential gate and the scratch negative/positive control

   The fix was validated three ways, in this order:

   (a) landed-lane byte stability: dry re-render of (1,0) (row 1) and
       (2,3) (negative-im row) under the fixed renderer -- 950/950 files
       byte-stable plus umbrella stable, exit 0, ~26 s per lane;
   (b) predicted-drift signal: dry (5,6) read 760/950 with the drifted set
       exactly the 190 `C1RouteAPanelTrueBall*` modules and nothing else;
   (c) post-emit dry re-run on each of the six re-emitted trees: 950/950
       byte-stable each.

   Scratch control (WSL driver `_probe/repro_2664_node_spell.sh`, minimal
   modules importing only the capture, deleted after the run, residue
   checked):

   +----------------+--------+--------+--------+--------------------------+
   | module         | exit   | footer | errors | signature                |
   +----------------+--------+--------+--------+--------------------------+
   | ...SpellBad2664  | 1    | 0      | 6      | "Not a definitional      |
   | (canonical)      |      |        |        | equality" at :21 and :27,|
   |                  |      |        |        | "Type mismatch" x2       |
   | ...SpellGood2664 | 0    | 1      | 0      | green, 0 uses sorry      |
   | (verbatim)       |      |        |        | (one scratch-writer      |
   |                  |      |        |        | newline warning)         |
   +----------------+--------+--------+--------+--------------------------+

   Logs: `_probe/repro_2664_node_spell_bad.log` /
   `_probe/repro_2664_node_spell_good.log`.  The bad side reproduces the
   batch signature exactly (same compiler, same error text at the pin and
   at the `rfl`); the good side replays the rows-5/6 pin shape kernel-clean.

5. Evidence table (batch build and census)

   Per entry: umbrella stage (heavy class, 4691-job plan), assembly stage
   (normal class, 4886-job plan), entry oleans, canonical digests
   (16-hex prefixes), census gates.  All stage footers read
   `Build completed successfully`, all error/sorry/sorryAx counts 0.

   +-------+---------+---------+-------+------------------+------------------+-------+
   | entry | umb (s) | asm (s) | olean | chain digest     | assembly digest  | gates |
   +-------+---------+---------+-------+------------------+------------------+-------+
   | (1,0) |   345   |    33   |  965  | 7bed2737c6b23187 | 964ea40b52da7e9e | 15/15 |
   | (1,4) |   292   |    29   |  965  | fc685d5a210c4b7a | 7ac5e3d64c5187d6 | 15/15 |
   | (2,3) |   291   |    28   |  965  | 9bafcb47169013f7 | ea7e489361958fbe | 15/15 |
   | (3,2) |   289   |    30   |  965  | 6ab2940cfc8a4305 | 55227351e851f4c2 | 15/15 |
   | (4,0) |   305   |    29   |  965  | 3cf99e282fb1a698 | d8887e492591a569 | 15/15 |
   | (4,1) |   287   |    30   |  965  | b8e739c5ce263193 | 454b5e76a8487d7b | 15/15 |
   | (5,6) |    98*  |    32   |  965  | 77d1016299e45454 | 354767d5e2570a8b | 15/15 |
   | (5,7) |   293   |    31   |  965  | b7932594f168400f | d04aa1f6c46bc17f | 15/15 |
   | (6,5) |   284   |    30   |  965  | b4cb4481e8225496 | 8a06bed14fc71b36 | 15/15 |
   | (6,7) |   289   |    30   |  965  | 0597e3127a1768d5 | e1f10346fdb30d31 | 15/15 |
   | (7,5) |   288   |    27   |  965  | 0120b313377a5d90 | 87d31b5c0c9d7769 | 15/15 |
   | (7,6) |   269   |    33   |  965  | 5b5539a657a3dd04 | 72ee2b636e91f34f | 15/15 |
   +-------+---------+---------+-------+------------------+------------------+-------+

   (*) (5,6) is the RESUMED entry: its first umbrella attempt failed
   (section 2), and the relaunch recompiled only the 190 changed trueball
   modules while the 760 node-independent family modules replayed from
   cache -- 98 s versus the ~290 s fresh-entry wall.  The resumed batch ran
   six entries in 33 min 29 s (00:53:48Z -> 01:27:17Z).

   Per-entry artifacts: `results/2664_assembly_{R}_{C}.json` (15 gates
   each: two-sided byte equality, footer, zero errors/uses-sorry/sorryAx,
   exact axiom trio records, fresh print-count match, replay cross-build
   vs the umbrella, 15 new module oleans, 965 entry oleans, membership
   shape, member-record trio) and `results/2664_build_{R}_{C}.json`
   (driver-attested + whole-log reconciliation, sizes, warning
   breakdown).  Umbrella warning lines: 80 per entry = 3 Lake package
   local-changes notices + 76 pre-existing ConnesWeilRH/Source warnings +
   exactly 1 entry-path warning (the frozen template's Tiling
   `style.show`).  1739 umbrella axiom records + 1858 assembly records,
   all on the exact trio, no nonstandard record.

6. Acceptance method

   Log-not-exit-code throughout: verdicts were read from the whole WSL
   resource-runner logs (footer, job counts, error/uses-sorry/sorryAx
   counts, axiom-record brackets vs `[propext, Classical.choice,
   Quot.sound]`) and reconciled against the driver-attested per-stage
   lines by `_probe/assemble_2664_build_evidence.py R C`; the census
   (`_probe/assemble_2664_asm_evidence.py R C`) recomputes the 15 gates
   from both sides' module bytes, the two logs, and the olean census, and
   writes the assembly artifact.  Exit codes, task-notification statuses,
   and batch-level OK lines are not evidence on their own.

   Provenance: the fixed `gen_2664_entry.py` hash (`c3199d0c107c1c8e...`)
   rides the (5,6)/(5,7)/(6,5)/(6,7)/(7,5)/(7,6) entry payloads; the six
   first-attempt entries' payloads carry the pre-fix generator hash
   (`74f16f8e...`) while their trees were dry-verified byte-identical
   under the fixed generator -- the recorded generator-hash lag (AGENTS
   2cu), resolved by the byte gates, not by hash equality.

7. Scope and next

   The manifest `results/2664_offdiag_manifest.json` now carries 15
   entries (14 psi=0 + (29,3)), every chain digest disk-verified; the
   deferral recorded in `results/2664_build_0_4.json` is resolved.  Next per
   the committed plan: the wave protocol over the survey's remaining
   classes -- 833 degree-55 entries (member (0,3) already landed, written
   before the parameterized lane) and 23 ladder entries needing
   58/60/63/66/70-rung degrees (member (29,3) is wave-1) -- with the
   per-wave byte re-verification and manifest refresh.  This record closes
   the psi=0 branch only: no entry partition sum beyond one entry, no
   producer margin, no `SourceRH`, no RH claim.
