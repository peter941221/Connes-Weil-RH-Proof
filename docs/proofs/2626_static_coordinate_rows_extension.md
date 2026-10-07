Record 2626: static defect comparison rows 6-29 certified
Date: 2026-10-07

Result

The result is positive: rows 6 through 29 of the static defect
comparison now carry the record-2617 coordinate-leaf certificate shape,
completing the static layer - with row zero (record 2617) and rows 1-5
(record 2623), all thirty rows and all 900 matrix entries are
individually certified. This batch adds 720 verified entries; the
validator emits STATIC_COORDINATE_ROWS_EXTENSION_PASS after 5112
serial module builds, checking 720 cell audits plus 24 row audits,
each reporting exactly
[propext, Classical.choice, Quot.sound]. The full static comparison is
not yet assembled into a single consumer theorem, the analytic
containment premise stays open, and actual coefficient membership is
not proved; producer GO and RH remain false.

Each row reuses the row-zero construction unchanged: the sharded exact
product cache, the six-block sum modules importing the generic block
exactly once, four coordinate sums per entry, direct entry bounds with
audits, and the same-name row facade that keeps the record-2600
consumer names (candidateInverseDefectEntryBound2600_row_XX). The
twenty-four row facades replace their source-only record-2600 monoliths
under the same names, exactly as rows 1-5 did in record 2623. The
generator's converted-row gate was extended from rows 0-5 to all thirty
rows, and the primary selftest gate re-verifies that rows 0-5 and row
zero regenerate byte-identically before and after the builds - the row
extension must not disturb certified rows.

Batch scale

This is the coordinate-leaf shape at its full extent: 24 rows in one
validation, roughly five times the record-2623 batch, with the 2600
payload shards (rows 0-9, 10-19, 20-29) supplying the shared exact
data. Five thousand one hundred twelve modules compile serially through
the resource runner with the pinned v4.30.0 toolchain and
workspace-local Mathlib packages: 8904 seconds (2.47 hours) of total
compiler wall time with peak RSS 6.3 GiB - linear in the record-2623
per-row cost (about 371 seconds per row versus 339 there), with no
memory-wall regression at five times the batch size. The same-name
facade replacement is re-verified end to end: rows 0-5 and row zero
regenerate byte-identically before and after the builds, and every
parent and new source/object is re-hashed at run end.

The validator hash-checks all record-2623 prerequisite stages and their
record-2617 parent link, requires the upstream objects present,
byte-regenerates the twenty-four rows before and after the runs, runs
the nine selftests (row-zero regression, committed-rows 1-5 regression,
independent straight-loop bounds on sampled new rows, scope
disjointness, LF hygiene, facade names, dependency-chain law, negative
controls), builds the modules serially through the resource runner, and
audits every cell and row theorem.

Primary evidence:

  scripts/generate_static_coordinate_bounds_2617.py (converted-row gate)
  scripts/generate_static_coordinate_rows_2623.py (--rows 6,...,29)
  scripts/static_coordinate_rows_selftest_2626.py
  scripts/validate_static_coordinate_rows_2626.py
  ConnesWeilRH/Dev/C1RouteACorrectionStaticDefect*Row{06-29}*.lean
  results/2626_static_coordinate_rows_validation.json

Reproduction interface

Run scripts/validate_static_coordinate_rows_2626.py in Linux with
--workspace pointing at a toolchain-pinned workspace seeded from the
all-Linux library (holding the certified 2623 objects and the compiled
2600 payload shards) and --logs at the log directory. The validator
emits STATIC_COORDINATE_ROWS_EXTENSION_PASS only after tests, all
builds, exact axiom audits, and end-of-run freshness checks.

Next steps

1. Assemble the full 900-entry static comparison into a single consumer
   theorem and attach it to the 2601 integrated certificate's premise
   list.

2. Keep the analytic containment premise moving (record 2624's pricing
   lane): complex scalar engine, then the pilot entry (0,3) at degree
   55; assemble the (0,0) partition from the 180 certified panels
   (record 2625).

3. With both scaling bricks landed, the remaining 2601 premises are
   concrete named objects - enumerate what is left before attempting
   the integrated-certificate assembly.
