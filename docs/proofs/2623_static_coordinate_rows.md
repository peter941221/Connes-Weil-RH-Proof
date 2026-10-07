Record 2623: static defect comparison rows 1-5 certified
Date: 2026-10-07

Result

The result is positive: rows 1 through 5 of the static defect comparison
now carry the record-2617 coordinate-leaf certificate shape, with 150 of
the 900 matrix entries verified. The validator emits
STATIC_COORDINATE_ROWS_COMPARISON_PASS after 1065 serial module builds,
checking 150 cell audits plus 5 row audits, each reporting exactly
[propext, Classical.choice, Quot.sound]. The remaining 24 rows, the
analytic containment premise, and coefficient membership stay open;
producer GO and RH remain false.

Each row reuses the row-zero construction unchanged: the sharded exact
product cache, the six-block sum modules importing the generic block
exactly once, four coordinate sums per entry, direct entry bounds with
audits, and the same-name row facade that keeps the record-2600
consumer names (candidateInverseDefectEntryBound2600_row_XX). The
row-zero emission is byte-regressed against the committed record-2617
files as the primary gate, and an independent straight-loop engine
recomputes sampled entry bounds; negative controls reject perturbed
inverse entries and out-of-range indices.

Why this row batch closes the remaining 2600 wall

The record-2600 monolith grew the full 30x30 interval matrix thirty
times per row theorem and was killed three times by monotonic
anonymous-memory growth (up to 187G swap). The coordinate-leaf shape
removes that unfold entirely - four coordinate sums per entry, direct
bounds - and this batch shows the shape holds at batch scale: 1065
modules compile in 1695 seconds of total compiler wall time with peak
RSS 6.4 GiB, two orders below the wall. The three 2600 payload shards
(rows 0-9, 10-19, 20-29) compiled green before the batch in
201s/41s/14s, confirming the def/theorem-unit split.

Build and validation facts

The workspace practices recorded in AGENTS 2by are load-bearing here:
the toolchain pin in the workspace root (a toolchain-less cwd makes the
elan shim resolve the default toolchain, whose newer compiler rejects
every pinned v4.30.0 object), the seed from the all-Linux-built
library, and the workspace-local Mathlib package copy (reading Mathlib
objects through the /mnt/c 9p mount costs minutes per module on a cold
VM; on ext4 the batch paces near 2.4 seconds per module). One legacy
byte pin was honored rather than rewritten: the record-2617 source hash
of Row00Col00 is the CRLF variant of its content, so that file keeps
its pinned disk state and the content-level regressions normalize line
endings on both sides before comparison.

The validator hash-checks all 214 record-2617 prerequisite stages,
requires the upstream objects present, byte-regenerates the five rows
before and after the runs, runs the nine selftests, builds the 1065
modules serially through the resource runner, and audits every cell
and row theorem. Rows 6 through 29 remain uncalled; the row batch does
not touch the matrix, the candidate inverse, or any analytic claim.

Primary evidence:

  scripts/generate_static_coordinate_rows_2623.py
  scripts/static_coordinate_rows_selftest_2623.py
  scripts/validate_static_coordinate_rows_2623.py
  ConnesWeilRH/Dev/C1RouteACorrectionStaticDefect*Row0[1-5]*.lean
  results/2623_static_coordinate_rows_validation.json

Reproduction interface

Run scripts/validate_static_coordinate_rows_2623.py in Linux with
--workspace pointing at a toolchain-pinned workspace seeded from the
all-Linux library (with the 2600 payload shards compiled) and --logs at
the log directory. The validator emits
STATIC_COORDINATE_ROWS_COMPARISON_PASS only after tests, all builds,
exact axiom audits, and end-of-run freshness checks.

Next steps

1. Extend the batch to rows 6-29 in five-row chunks; per-row cost is
   now measured at roughly 340 seconds of compiler wall time.

2. When all thirty rows are certified, assemble the full 900-entry
   static comparison and attach it to the 2601 integrated certificate's
   premise list.

3. Keep the analytic containment premise (record 2624's pricing lane)
   moving in parallel: complex scalar engine, then the pilot entry.
