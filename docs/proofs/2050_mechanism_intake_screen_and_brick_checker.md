# 2050 — Instrument layer: mechanism intake screen and mathlib brick checker registered

Verdict: **INSTRUMENTS-REGISTERED** (no probe, no measurement).  Two
reusable tools enter the ledger: the record-2047 antibody table is now
executable as an intake screen
(`scripts/mechanism_intake_screen.py`), and "does the pinned mathlib
have X?" is now a one-command evidence producer
(`scripts/mathlib_brick_check_2049.py`, artifact
`results/2049_mathlib_brick_check.json`).  Six instrument laws are
recorded from this batch's own failures.

## 1. The intake screen (record 2047 table, executable)

```
python3 scripts/mechanism_intake_screen.py SKETCH.md [SKETCH2.md ...]
python3 scripts/mechanism_intake_screen.py --demo --json OUT.json
```

The tool embeds the ten antibody classes (SPLIT, PRE, CHAN, IND, TRUNC,
STAB, TEST, VAC, GAP, INDEF) plus the two 2047 additions (DH, RT), each
with its one-line firing rule, its ledger exhibits, its action, and a
keyword pattern set.  HONEST SCOPE, stated in the tool header and
repeated here: it is a triage aid over PROSE.  A fired class means "read
the cited exhibit and check whether it applies", never "this mechanism
is dead".  Verdicts come from the exhibits, not from the script.

Demonstration run (`--demo`, artifact
`results/2050_intake_screen_demo.json`):

```
+-------------------------------------------+---------------+-----------------------------------+
| demo input                                | classes fired | reading                           |
+-------------------------------------------+---------------+-----------------------------------+
| FE-only stowaway (synthetic)              | PRE, VAC, DH  | three genuine hits: read 1995,    |
|                                           |               | 1411 and DH at intake             |
| compression-sign (synthetic)              | TRUNC, INDEF  | INDEF is genuine (2045 no-go);    |
|                                           |               | TRUNC is a VOCABULARY hit only    |
|                                           |               | ("truncated operator" in passing, |
|                                           |               | no verdict is read off it) - the  |
|                                           |               | documented false-positive mode    |
| panel-local model (record 2046 s4, live   | (none)        | the live candidate passes intake  |
| candidate)                                |               |                                   |
+-------------------------------------------+---------------+-----------------------------------+
```

The third row is the tool's usefulness test: a genuinely new mechanism
sketch fires nothing, so the screen does not obstruct work.  The second
row is its honesty test: a vocabulary coincidence fires a class that the
exhibit check immediately dismisses, so the screen is never a decision.

## 2. The mathlib brick checker

Single-pass scan of `.lake/packages/mathlib/Mathlib` (pinned rev
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, toolchain
`leanprover/lean4:v4.30.0`), table-driven, one row per brick, evidence
reported as `file:line`.  Seven rows registered this batch (verdicts and
full evidence in record 2049 section 3 and the artifact); the design
constraints that matter:

- patterns must be WORD-BOUNDARY ANCHORED: an unanchored `trace_mul_le`
  matched `Matrix.ext_iff_trace_mul_left` (a false PRESENT on the von
  Neumann row) - the incident is recorded in the tool's own docstring;
- the scan must be single-pass: seven independent tree walks over 8000+
  files is minutes of I/O for no reason;
- stdout must be ASCII-SAFE: the mathlib source carries blackboard-bold
  and arrow characters and the Windows console here is GBK-coded
  (`UnicodeEncodeError` on the first run; the JSON is unaffected).

## 3. Instrument laws recorded this batch

1. **Whole-repo or nothing.**  A claim of the form "the literature item
   is not in the ledger" must be produced by `git grep` over the whole
   repo on the bare identifier.  The record-2045/1347-1348 incident
   (nine pre-existing files, earliest 15 days before the claim) is the
   exhibit; a subtree grep with narrow patterns is not evidence.
2. **Word boundaries for identifiers.**  Lemma-name and symbol greps
   need `\b` anchoring (section 2, first bullet).
3. **Gates at the design's own floor, every time.**  This batch produced
   the third instance in two days: the A3 float64 echo was gated at
   `1e-12` relative when the block values are differences of O(1)
   trigonometric evaluations and therefore carry an ABSOLUTE floor of a
   few ulps of 1 (~1e-15), independent of h and omega; relative-to-block
   measures blow up when the block passes through a zero.  The gate now
   sits on the absolute floor with the scaling table in the record
   (2048 section 5).  Diagnosis by scaling, never by loosening.
4. **wsl.exe output goes to a log file, not through a pipe.**  The first
   probe of this batch lost its timing digits to the UTF-16/null-byte
   encoding of wsl.exe (the pipe turned binary and the numbers vanished
   behind "Binary file (standard input) matches").  Acceptance is the
   log content, read from the file.
5. **Gate failures are adjudicated against structural bounds before any
   tolerance is touched.**  The 2048 A3 independent product-rule check
   carried a transcription bug (its first term was missing `/om`) while
   its own comment stated the formula correctly; the coded term then
   exceeded its analytic ceiling `|h sin(om b)/om| <= h/om` by 4.3x,
   which identified the CHECKER -- not the checked closed form, which
   agreed with mpmath quadrature at 2.42e-27 -- as the defect.  A
   relative-only gate would have blamed the closed form.  The rig now
   carries the ceiling as an explicit assertion (2048 section 4, item 1).
6. **Cheap diagnostic paths must replicate the full path's call order.**
   The 2048 `--a3only` path runs A3 in 0.3 s against 285 s for the full
   probe and localized the transcription bug only because it preserved
   the real run's ordering (quadrature first, product form after).

## 4. Registration and non-claims

- Tools: `scripts/mechanism_intake_screen.py` (record 2050 table),
  `scripts/mathlib_brick_check_2049.py` (record 2049 table).
- Artifacts: `results/2050_intake_screen_demo.json`,
  `results/2049_mathlib_brick_check.json`.
- Use at intake: run the screen on any new mechanism sketch before it
  costs desk time; run the brick checker before any Lean-side plan that
  rests on "mathlib has X".
- Non-claims: the screen is not a decision procedure and neither tool
  carries mathematical authority; both are instruments.  The brick
  checker reads SOURCE, it does not build Lean.  No probe, no theorems,
  not RH.