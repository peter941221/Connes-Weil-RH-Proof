# 2453 - Owner containment import at 11 positions; norm bridge landed, node-norm attachment open

Date: 2026-10-02.

Verdict in one line: the 2452 hypothesis-class door now admits the
whole certificate position set - the captured owner is bound into Lean
at the nine exact binary64 positions of the 2445/2449 endpoint
certificate plus both strip endpoints ±1/2, and Lean proves the
30-family sum containment for both channels at every position (22
theorems, standard three axioms); the generic norm bridge
`norm_le_of_rect_mem_2453` (rectangle containment ⇒ ‖z‖ ≤ sum of corner
maxima) is a new committed Lean asset, but the step that would attach
the per-position numeric bounds N inside Lean hit a simp expansion loop
and is registered as the open seam.

## What was delivered

- `ConnesWeilRH/Dev/C1RouteANormBridge2453.lean`: the consumer-side
  bridge `(ComplexRect2427.Mem z r) → ‖z‖ ≤ max |r.reLo| |r.reHi| +
  max |r.imLo| |r.imHi|`, proved from
  `Complex.norm_le_abs_re_add_abs_im` by sign case analysis; no square
  root, so a generator can emit the exact rational target. Axiom trio
  verified.
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeNormImport2453.lean`
  (machine-generated, 437 KB): exact dyadic coefficient/modulation
  literals from the 2275 capture; per position p00..p10 the bump and
  phase rectangle arrays (2^-200 outward margins, zero box at
  outside-support families, |pos| ≥ width² rule), and per position and
  channel the containment theorem
  `correctedPhysical_mem_pos2453{Base,Corr}{tag}` proved through
  `externalFamilyValue_mem_of_factor_cert2437` and
  `correctedPhysical_mem_of_family_rect2436` - the 2452 proof shape,
  unchanged and now at 22 instances.
- Position set (sorted, exact): ∓6.5536, ∓4.9152, ∓3.2768, ∓1.6384 as
  exact binary64 rationals (denominators 2^46/2^47/2^48), ∓1/2, and 0.
  Cross-record check: the base-channel sum box at +1/2 is
  0.862481584 + 0.091090408 i, bitwise-consistent with the 2452 point
  import at the same position.
- `results/2453_owner_node_norm_import.json`: per position and channel
  the composed sum rectangles as exact decimal strings and the
  node-norm bound N = max|re| + max|im| (e.g. base at ±1/2:
  N ≈ 0.9537/0.9536; corr at +1/2: N ≈ 28.92; at ±6.5536 all families
  sit at the support edge and N ≈ 1e-45-scale residuals); 660/660
  reference-point containment checks with zero failures.

## Verification

Producer: regenerates everything from the 2275 capture and the 2445
certificate at dps 90, checks each composed four-corner hull against
the exact rational reference term (660 checks, 0 failures), writes the
module, probe, audits and artifact. Pin: re-derives every literal from
the same sources with the producer's exact arithmetic order, parses
and binds them bitwise, recomposes all 44 sum rectangles and all 22 N
bounds independently, binds the module sha, and fires three mutation
controls (shifted phase box, perturbed norm record through the same
N-binding detector, truncated module):
PINNED-OWNER-NODE-NORM-IMPORT-VERIFIED, zero failures.

Builds on the rebuilt ext4 mirror (fresh clone 9350569a + transplanted
.lake, offline): probe (position p05 = 0, both channels) 37 s green;
full module + audit green, all 22 containment theorems plus the bridge
theorem on exactly [propext, Classical.choice, Quot.sound] (3713
jobs). Bridge audit module green (1488 jobs replay). Windows and
mirror copies byte-identical.

## The open seam: Lean-side node-norm attachment

The bridge theorem consumes a rectangle value; the 2389/2390 scalar
consumers need the N bound stated against the actual sumFinset term.
Emitting that as a Lean defeq chain (unfold the 30-term array sum to
literal corners via `Fin.sum_univ_succ`, `Matrix.cons_val_zero/succ`,
`Fin.sum_univ_zero`, then `norm_num` against the emitted N) hits a
simp rewrite loop: even `Simp.Config.maxSteps := 50000000` is exceeded
instantly, i.e. the failure is a loop, not linear work. Three
escalations were tried and stopped honestly: larger heartbeat budgets,
explicit lemma lists, and isolated `Fin 5` scaffolds (the small cases
close; the 30-term exact-rational case loops). Registered paths
forward: a `norm_num` extension evaluating rectangle arithmetic
directly, per-family literal rect decomposition with `mem_add` chains,
or an emit-the-proof-term generator. Until then the numeric N bounds
live at artifact + pin grade, with the Lean bridge ready as their
consumer.

## Environment (this session)

The drifted ext4 mirror was rebuilt as a real git clone at 9350569a
with the complete .lake transplanted (mathlib pin unchanged); WSL NAT
mode cannot reach github.com, so the offline workflow is
clone-on-Windows + transplant, validated by a 3712-job clean build
with the 2452 axiom trio. Old tree preserved at a sibling path, nothing
deleted. Known residual: plausible/LeanSearchClient packages report
mode-bit dirt in the mirror (cosmetic, registered).

## Scope

Eleven positions, containment only. The bump and phase fields remain
hypotheses by design; no strip norm, no quadrature import, no signed
selected-detector budget, no producer GO and no RH claim follows.

Evidence:

- `scripts/routea_owner_node_norm_import_2453.py`
- `scripts/routea_owner_node_norm_import_2453_pin.py`
- `ConnesWeilRH/Dev/C1RouteANormBridge2453.lean`
- `ConnesWeilRH/Dev/C1RouteANormBridge2453Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeNormImport2453.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeNormImport2453Audit.lean`
- `results/2453_owner_node_norm_import.json`
- `results/2453_owner_node_norm_import_pin.json`
- `build-logs/2453_owner_node_norm_import.log`
