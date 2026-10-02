# 2452 - First actual-owner point import through the hypothesis-class door

Date: 2026-10-02.

The 2433 directed-value containers, the 2437 three-factor family
interface and the 2436 owner consumer existed as pure plumbing; no
concrete numbers of the actual owner had ever passed through them. This
record performs the first end-to-end point import: the captured owner
(2275) is bound into Lean as exact literals at the evaluation point
x0 = 1/2, the per-family factor rectangles are produced externally with
outward margins, and Lean proves the 30-family sum rectangle contains
`correctedPhysical` for both channels.

## Statement

For each family k, `externalFamilyValue2344` factors as
coefficient x bump x phase. The import packages

- the coefficient as a degenerate point box around its exact dyadic
  literal (`ComplexRect2427.point_mem`, proved in Lean, no arithmetic);
- the bump `widthBump (storedWidth k)^2 (1/2)` inside an exact rational
  box with margin `2^-200` (hypothesis class 2433);
- the phase `Complex.exp (capMod2452 k * (1/2) * Complex.I)` inside an
  exact rational box with the same margin (hypothesis class 2433);

composes them through `externalFamilyValue_mem_of_factor_cert2437`, and
consumes the 30-family sum through
`correctedPhysical_mem_of_family_rect2436`. The four new theorems
(`familyRect2452_mem_base`, `familyRect2452_mem_corr`,
`correctedPhysical_base_point_mem_2452`,
`correctedPhysical_corr_point_mem_2452`) depend on exactly
`[propext, Classical.choice, Quot.sound]`.

## Verification

The producer regenerates every certificate from the capture at dps 90
(single exact-Fraction exponent, one division, then mpmath), checks the
composed four-corner hull against exact rational products of the box
centres for all 60 channel-family pairs (zero failures), and writes the
module plus artifact. The independent pin check re-derives the boxes,
parses every Lean literal, binds them bitwise, re-checks strict
containment, verifies the module sha against the artifact, and fires
three real mutation controls (shifted phase box, perturbed coefficient,
truncated module) through the same detectors:
PINNED-OWNER-POINT-IMPORT-VERIFIED, zero failures. The float display of
the base-channel sum box at x0 = 1/2 is
`0.8624815837902781 + 0.09109040786330272 i` with interval width near
1e-57.

The focused build completed 3712 jobs with zero error lines and the
four audited theorems on the standard three axioms; the generated
module disables only the long-line linter for its machine-generated
literals. Windows and mirror copies of the two new sources are
byte-identical.

## Environment incidents found and fixed en route

- The mirror's mathlib checkout showed 8729 modified files that were all
  permission-bit changes (0 insertions, 0 deletions) from the Windows
  sync; `core.fileMode false` restored a clean checkout. This unblocks
  the 2354 consumer replay.
- In this invocation path `$PWD` expands to the launch directory even
  after a preceding `cd`, so the resource wrapper received the /mnt/c
  workspace on the first builds. Explicit absolute `--workspace` paths
  behave correctly. Historical runner logs confirm the sanctioned
  workspace is the ext4 mirror; tonight's green builds ran on the
  /mnt/c tree with the same Linux toolchain and committed sources, and
  the ext4 mirror itself turns out to be a drifted partial copy
  (source-only ConnesWeilRH subtree, no git, stale build directory,
  foreign .git above it). Rebuilding a clean ext4 mirror is registered
  as the standing environment item before the next consumer-replay
  batch.
- Two background chains briefly shared one build log because a pipeline
  to `head` swallowed the pin script's exit status; the second chain
  then rebuilt the same module. Logs and verdicts of the final run are
  the authoritative ones.
- The pin check initially recomputed the exponent with a different
  rounding order and flagged two bump boxes; the binding is bitwise, so
  the pin now reproduces the producer's exact arithmetic order, while
  numerical independence lives in the margin-based containment checks.

## Scope

One point, one import exercise. The bump and phase containment fields
remain hypotheses by design; no strip norm, no quadrature import, no
signed selected-detector budget, no producer GO and no RH claim follows.
The tightening path (tight external factor certificates on strip nodes,
then integral-side import) now has a verified door to walk through.

Evidence:

- `scripts/routea_owner_point_import_2452.py`
- `scripts/routea_owner_point_import_2452_pin.py`
- `ConnesWeilRH/Dev/C1RouteAOwnerPointImport2452.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerPointImport2452Audit.lean`
- `results/2452_owner_point_import.json`
- `results/2452_owner_point_import_pin.json`
- `build-logs/2452_owner_point_import.log`
