Record 2636: owner-02 entry-(2,2) membership certificate (K02 panel family + assembly probe)
Date: 2026-10-10

Result

Positive at single-entry scope. The full K02 owner-02 stack — 541
PanelScalars / PanelTable / ActualPanel family modules, the regenerated
edge pair ScalarEdge2620K02 / ActualEdge2620K02, and the assembly probe
`ConnesWeilRH/Dev/ZProbe2628K02.lean` (213 theorems) — compiled green on
the Linux-native workspace in ONE xargs batch: 544 targets, 411 s wall,
4278-job graph, exit 0. Triple file-level acceptance on the batch log:
persisted oleans present for all 544 modules (1088 artifacts, 2 per
module, matching the K00 census ratio), full build-log error list empty,
`uses sorry` count zero. Deliverables:
`actualOwnerMomentMatrix2351_entry02_mem2628` — the 2597 entry-(2,2)
analytic interval contains the owner moment integral in all four
coordinates — plus the real-side error bridge `actualFullRealError2628K02`,
the four support theorems, the chunked replay chain, and the extraction
interface `entry02Interval2628` + kernel-rfl bridge.
eps = 251713554058321 / 1.25*10^153; edge charge 2/10^67.

Scope

Third of the 30 diagonal entries, and the FIRST owners >= 1 validation of
the parameterized generator beyond the hand-built K04: every owners >= 1
mechanism (succ-chain hsucc bridge, per-owner edge pair, cons_val lemma
insertion) is now machine-generated and build-verified. The remaining 27
diagonal entries, the partition assembly, the static consumer, the complex
scalar engine, Producer GO, SourceRH, and RH all remain open. No route
ruling changed.

What was new relative to 2635 (owner 0)

- Edge pair regenerated per owner: `scripts/generate_moment_edge_owner_2628.py`
  emits the 2620-generator Edge module (renamed through the 2628 wrapper)
  plus the record-2634 ActualEdge module shape, with the single-digit
  decimal bound computed EXACTLY from the rounded Expected literals
  (minimal k with prod * 10^k >= 1, then the ceiling digit). Regression
  gate before generation: owners 0 and 4 reproduce the committed bounds
  2/10^68 and 5/10^65 bitwise; owner 2 then priced 2/10^67.
- cons_val family: Mathlib's VecNotation unfold lemmas stop at
  cons_val_four, so owners 1..4 insert `Matrix.cons_val_{one..four}` into
  every norm_num set; owners >= 5 need a project-local lemma family before
  family generation (the wrapper raises with that instruction).
- succ-chain bridge at index 2: `have hsucc : (analyticMomentInterval2597
  2 2) = (analyticMomentInterval2597 (Fin.succ (Fin.succ 0)) (Fin.succ
  (Fin.succ 0))) := rfl`, closing by kernel reduction — the record-2634
  shape at a new index, generated for the first time.

Preflight before the build (mechanical checks, all passed): token-stream
identity of the emitted def body against the 2597 row_02 element;
succ-chain shape in both slots of hsucc; per-field paren-insensitive value
identity of the four rfl bridges; import closure 589 = 544 K02-self + 45
shared, all shared modules committed (hence already in the mirror).

Incident — preflight checker formatting traps (two false alarms, no
probe defect)

The four bridge-value checks first reported False twice, both times on the
checker, not the probe: (1) the generator's succ_chain_text renders
`( (Fin.succ  (Fin.succ 0)) )` — a double paren wrap with an extra space —
while the committed K04 probe uses the single-wrap spelling; the terms are
identical and the chain's correctness is discharged by kernel rfl at build
time regardless of spelling. (2) the 2597 row_02 element itself writes its
fields as `((NUM : ℝ) / DEN)` (double wrap + numerator ascription), so a
verbatim-token comparison against the probe's `(NUM : ℝ) / DEN` capture
differs by one paren layer. Law: bridge-value preflight must be
paren-insensitive (strip `(NUM : ℝ)` ascriptions and all parens, then
compare token streams); paren SPELLING differences between the generator
and the hand-built reference are cosmetic and policed by rfl, not by the
preflight.

Next obligations

1. Remaining 27 diagonal entries (d = 3, 5..29): d = 3 is a direct
   --owner-index 3 rerun; d >= 5 first needs the project-local
   cons_val_{N} lemma family (Mathlib stops at four).
2. Partition assembly closure: consume the entry certificates in the
   owner-matrix partition statement.
3. Static consumer, then the complex scalar engine (record 2624 GO route:
   degree-55 complex polynomial, exp(i psi c) rotation mandatory).
