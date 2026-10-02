# 2454 - Owner node-norm bounds at Lean theorem grade (11 positions, both channels)

Date: 2026-10-02.

Verdict in one line: the open seam of record 2453 is closed - the
per-position node-norm bounds are now Lean theorems: for every one of
the 11 import positions and both channels,
`nodeNorm2454{Base,Corr}{tag}` proves
`‖correctedPhysical capCoef capMod pos‖ ≤ N` with N an exact rational
(the sum of corner maxima of the composed 30-family outer hull), all 23
new declarations on the standard three axioms.

## Statement and architecture

The 2453 bridge (`norm_le_of_rect_mem_2453`) reduced a norm bound to
corner maxima of a containing rectangle; the missing piece was a
containing rectangle whose corners Lean can evaluate. The 2454
generator emits, per position tag p00..p10 and channel:

- `hullRect2454{ch}{tag}`: a literal outer-hull array - per family the
  composed four-corner hull of coefficient x bump-box x phase-boxes,
  computed with the producer's exact interval semantics (same
  arithmetic order as 2453, same 2^-200 margins, zero box outside
  support);
- `familyHull2454{ch}{tag}f00..f29`: per-family containment theorems
  transporting the 2453 product rectangle into the literal hull through
  the new generic one-sided lemma `mem_of_rect_subset_2454`
  (corner-wise covering + containment transports); the four corner
  comparisons are discharged by `rfl`-based array peels at the concrete
  index (no simp numeral peeling), structural interval-algebra
  unfolding, and one `norm_num` on the conjunction;
- `chainRect2454{ch}{tag}`: the right-associated `.add` chain of the 30
  hulls, and `sumMem2454{ch}{tag}`: its membership for
  `correctedPhysical`, assembled from the per-family theorems by an
  explicit `ComplexRect2427.mem_add` chain under the unfolding of the
  30-term sum through the new generic bridge lemma
  `fin30_sum_univ_chain_2454` (the sum equals the right-associated
  numeral-indexed chain, proved once over an abstract summand);
- `nodeNorm2454{ch}{tag}`: the norm bound, by
  `le_trans` through the 2453 bridge and a final step that peels the
  chain to literals via `rfl`, unfolds `.add`, and lets `norm_num`
  evaluate max|ΣreLo| |ΣreHi| + max|ΣimLo| |ΣimHi| ≤ N.

The N values (exact rationals, ~300-420 decimal digits) match the 2453
artifact bitwise (base ±1/2 ≈ 0.9537/0.9536, corr +1/2 ≈ 28.92, support
edges ≈ 1e-45-scale).

## Verification

Producer: 660/660 reference containment checks; cross-record gate
against the 2453 artifact sum boxes: 0 mismatches (same capture, same
arithmetic order). Pin: re-derives hulls and N fresh, parses and binds
every literal bitwise (hull arrays, all 30 rfl-peel literals per
nodeNorm, all 14 literals per familyHull theorem, the N bound), binds
the module sha, fires three mutation controls (shifted hull corner,
perturbed norm record, truncated module):
PINNED-OWNER-NODE-NORM-BOUND-VERIFIED, zero failures.

Builds on the ext4 mirror: the bridge module (2 lemmas) and its audit
compile green; the generated module (4.77 MB, 3714 jobs) completes with
zero errors; the declaration audit prints the axiom trio for all 23
audited names (`mem_of_rect_subset_2454` + the 22 `nodeNorm` theorems)
with zero deviations. Windows and mirror module copies are
byte-identical (sha256 c1b0b0e8..., bound by the artifact).

Two build incidents were caught and fixed before the green state, both
worth recording:

- Stale-module incident: the first full build failed with 22 per-block
  type errors because the module on disk was an earlier producer
  generation (old tactic shape, including a generation typo) whose sha
  the artifact still bound as OWNER-NODE-NORM-BOUND-COMPLETE. Lesson:
  an artifact verdict attests producer-vs-artifact consistency, not
  compilability; after any producer edit, regenerate and re-pin before
  building.
- Doubled-head incident: the regenerated module still failed at the 22
  `sumMem` steps. The producer emitted
  `exact ComplexRect2427.mem_add {chain}` where `{chain}` is already a
  complete nested `mem_add` chain, so the head prefix turned the whole
  chain into a single first argument - a partial application whose
  mismatch message shows a phantom function arrow with fresh mvars
  (`Mem ?m ?n -> ...`) that reads like a unification failure. Fix:
  `exact {chain}`.

## Tactic-shape laws discovered en route

- Concrete-index array peeling must not be left to simp: `simp only`
  with cons lemmas peels small indices but stalls mid-array at larger
  ones (observed at index 14 of 30 with interval trees in the goal).
  The robust form is `have h : arr i = <literal> := rfl; rw [h...]` -
  definitional iota reduction, index-size independent.
- Closing `∑ i : Fin 30, f i` into the explicit numeral chain: state
  the chain over an ABSTRACT `f` in a small generic lemma and `rw` it
  instantiated. Closure is
  `simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]; rfl`:
  `add_zero` is mandatory (the `Fin.sum_univ_zero` residual leaves a
  trailing `+ 0`), and the final `rfl` is mandatory because simp's
  defeq check runs at reducible transparency and cannot fold the
  `Fin.succ`-chain indices into numerals (default-transparency `rfl`
  can). The lemmas live in `Mathlib.Algebra.BigOperators.Fin` (built in
  the transplanted .lake); `...Group.Finset` has no olean there.
- A complete nested application chain must be emitted as
  `exact {chain}`, never re-prefixed with its head constant (see
  doubled-head incident above).
- A `calc` step's tactic body at the same indentation as its `_ ≤` item
  misparses; prefer `refine le_trans ?_ ?_` with bullets, supplying
  `(b := ...)` explicitly when the intermediate bound is not
  syntactically pinned.
- mem_add chains must be assembled in the same association as the sum
  unfolding (f00 outermost, right-associated), or the leaves mismatch.

## Scope

Eleven positions, norm bounds only. The bump and phase fields remain
hypotheses by design; the hulls are import-side containers, not
endpoint strip norms; no quadrature import, no signed
selected-detector budget, no producer GO and no RH claim follows.
The next consumer step is the quadrature import: the per-node norms N
plus certified node spacing bound the endpoint strip integrals
(stripNorm at sigma = +-1/2), and those integral constants - not the
pointwise N directly - are the external hypotheses of the 2343
endpoint strip bridge.

Evidence:

- `scripts/routea_owner_node_norm_bound_2454.py`
- `scripts/routea_owner_node_norm_bound_2454_pin.py`
- `ConnesWeilRH/Dev/C1RouteANormBridge2454.lean`
- `ConnesWeilRH/Dev/C1RouteANormBridge2454Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeNormBound2454.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerNodeNormBound2454Audit.lean`
- `results/2454_owner_node_norm_bound.json`
- `results/2454_owner_node_norm_bound_pin.json`
- `build-logs/2454_owner_node_norm_bound.log`
- `build-logs/2454_owner_node_norm_bound_audit.log`
