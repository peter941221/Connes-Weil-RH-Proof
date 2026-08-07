# Proof-717 / Gate-3U: 842 — the Yoshida detector EXISTS (proved, axiom-clean); the REAL RH gap is the canonical Weil `≤ 0` sign, which the concrete space REFUTES; and Gate-3U's cross-branch `= 0` cancellation is a structural non-theorem

Date: 2026-08-07 · Status: audit verdict (source-verified; the structural claims
need no new build). This answers "1、2都做" and the "3U 还能不能打、怎么打"
question, and **corrects 841** on one point: 841 called Route-C's open floor "the
Yoshida pole-pairing detector EXISTS axiom". That is wrong — the detector exists
as a real axiom-clean construction. The true Route-C open input is a different
sign, and it is the SAME sign the Gate-3U route is missing.

SOURCE: `Source/CC20YoshidaConstruction.lean`, `Source/CC20YoshidaCriterion.lean`,
`Source/CC20TestSpace.lean`, `Route/CC20RouteRealization.lean`,
`Dev/UnconditionalSkeleton.lean`, `Source/CCM25Concrete/CCM24FiniteSCanonicalSupportGate3U.lean`.

## 0. Result (先讲结论)

**Two open inputs, ONE underlying number: the endpoint / half-density pole-sum sign.**

```
闭合 CC20 路线 (Route-C / Proposition C.1)     Gate-3U 路线 (3U)
──────────────────────────────────            ──────────────────────────────────
目标: ∀ρ off-line 无零点                    目标: canonicalRealGate3UAt (= ∥endpoint∥ ≤ 1)
需要:  (A) detector 存在   ✓ 已证 (axiom-clean, see §1)
       (B) canonical Weil ≤ 0  ← OPEN axiom
                                           需要: (a) unit-scale HS ✓ 已证 (839 axiom-clean)
                                                  (b) generic-λ HS Summable  ← OPEN axiom
```

**Finding 1 — the detector EXISTS is a THEOREM, not an axiom.** 
`normalizedCC20YoshidaDetectorExists` (CC20YoshidaConstruction:2715) is built from
the Vandermonde/matrix lemma `weighted_mellin_kernel_log_line_independence` (L942,
axiom-clean) plus finite-window Mellin interpolation
`fixed_window_node_value_image_mellin_surjective`. Its positive-Weil field
(`weilSumPositiveIfOffLine : 0 < weilLocalSum (⋆ g)`) is closed by
`concreteYoshidaMomentData_weilLocalSum_positive` (L2218). All three depend only on
`[propext, Classical.choice, Quot.sound]`, no sorryAx, no `*Root`. So 841's
"detector-exists axiom" label is a miscategorization.

**But the conclusion of 841 stands at the right layer once re-pointed:**
- The real Route-C open input is `axiom normalizedCoreCC20PropositionC1SourceCriterionRoot`
  (UnconditionalSkeleton:1564), which asserts `CC20PropositionC1SourceCriterion`,
  i.e. the canonical Weil **`≤ 0`** sign for every compact-smooth test vanishing on the
  finite Mellin set.
- The real Gate-3U open input is generic-λ HS: `hfactor : Summable ‖sourceProlateHilbertSchmidtFactor λ‖²` (839).

**Finding 2 — the same concrete space both proves the detector POSITIVE and REFUTES
the canonical condition. It is internally so:**
- `normalizedCC20YoshidaDetectorExists` (L2715): detector positive (proved).
- `not_normalizedCC20FiniteVanishingWeilCriterion` (L2474): REFUTES
  `CC20FiniteVanishingWeilCriterion normalizedCC20TestSpace cc20TripleFiniteVanishingSet`,
  whose underlying claim is canonical `≤ 0`.

The contradiction mechanism (L2293-2434): a `main`-built Mellin-interpolated test g
with vanishing Mellin at the three critical points, target Mellin value `(-1)` at the
probe rho (and at ±I/2), so that `starConvolution g`'s double-convolution half-density
pole = `(-4) + (-4) = -8 < 0`. The SAME `concreteYoshidaMomentData_weilLocalSum_positive`
feeds the detector's positive `weilLocalSum` and simultaneously violates any `≤ 0`
canonical bound. One number, two sign targets, mutually incompatible.

→ **The "two routes" are not two parallel gaps; they are the same endpoint sign
of the same functional, packaged twice.** Route-C / Gate-3U each separately axiom
a sign (`canonical ≤ 0`, respectively generic-λ `Summable`), and even those two are
two faces of one endpoint/half-density sign question.

## 1. Task (1) — detector exists is a theorem; the real floor is canonical `≤ 0`

### 1a. Detector existence (existence) is PROVED (audit-confirmed)

`Source/CC20YoshidaConstruction.lean`:
```
 942  theorem weighted_mellin_kernel_log_line_independence           — Vandermonde/matrix, axiom-clean
      L2188 exists_concreteYoshidaMomentData_of_node_value_image_mellin_surjective
      L2218 concreteYoshidaMomentData_weilLocalSum_positive : 0 < weilLocalSum (⋆ g)
      L2482 normalizedCC20YoshidaDetectorExists_of_moment_data
      L2715 normalizedCC20YoshidaDetectorExists
               : CC20YoshidaDetectorExists normalizedCC20TestSpace cc20TripleFiniteVanishingSet
```
Dependencies: only `[propext, Classical.choice, Quot.sound]`.

`Source/CC20YoshidaCriterion.lean`:
```
L213 cc20_proposition_c1_from_yoshida_detector
     Requires : CC20YoshidaDetectorExists ✓  + CC20FiniteVanishingWeilCriterion ← the open input
```
So from detector-exists + canonical `≤ 0`, we get RH. Detector is proved; the only
remaining Route-C input is `CC20FiniteVanishingWeilCriterion` (canonical `≤ 0`), and
that is refuted on the concrete space.

### 1b. Why "detector positive" is already there yet still stuck — the sign flips at the ends

The detector needs `weilSumPositiveIfOffLine : 0 < weilLocalSum (⋆ g)`. This positive
comes from `concreteYoshidaMomentData_halfDensityPoleSum_negative` (the double
convolution half-density sum = −8 < 0), negated: `weilLocalSum = −(half-density sum)`
> 0. So a test with negative half-density sum gives positive `weilLocalSum` (detector
ok) but violates any canonical `≤ 0` on `weilLocalSum`. Both targets are the same
quantity at the same half-density point; sign is the only difference.

### 1c. Why the concrete instantiations don't close the loop

`UnconditionalSkeleton.lean:1564` keeps `CC20PropositionC1SourceCriterion` as an
`axiom …Root` (a ∀-input existence, not a single object). Because the concrete space
REFUTES the criterion, no concrete witness can ever feed that `Root` honestly — it is
not "a wall at detector": it is "a sign that concrete space contradicts". So even with
detector proved, the canonical-≤­0 axiom stays open and is in fact not-true on the
concrete test space. To close it one must either swap the test space or weaken the
criterion to permit end zeros — a real analytic change, not a pipe.

## 2. Task (2) — cross-branch cancellation is a structural non-`=` theorem

- The ~30 gate theorems are all variants on `canonScalarRealGate3UAt` (a single
  metric gate), reached by many "judgment" theorems (`_iff_…Bound`, per
  `Dev/CCM24FiniteSCanonicalRealGateAudit:11-27`).
- **Grep `crossBranch|cancellation|*cancel|…` across `Source/**/*.lean` = 0 hits.**
  There is NO named theorem `forward + outer + secondSupport + prolate = 0`.
- `canonicalRealGate3UAt = ∥raw endpoint trace∥`(a bound), not an `= 0` cancellation;
  it is an input gate, not a cancellation output. The two-channel decomposition in
  memory (815/823) is never instantiated as an equality on the continuum.
- Every gate criterion also needs two premises: (i) generic-‑λ HS `hfactor : Summable` and
  (ii) some `∥…∥ ≤ bound`. Even with both, you get a bound `∥≤ 1∥`, not `= 0`.
  To get `= 0` you must push the bound to 0 while holding the exact − relative half
  -density pole gap near 0 — precisely the cross-branch arithmetic step that is missing.
- 837's `band: 0.847→0.886` growth is a diodometric asymmetry / bound slack, not a
  removable cancellation fact. On the continuum there is still no axiom-clean theorem
  `trace(…) = 0 `for the factor.

## 3. Verdict — can 3U still be fought, and how

### Can it be fought? Yes, and not by stacking generic-λHS.

Align the three open lines onto one quantity:

```
Route        target                          current state       real open face
─────────    ──────────────────────────────  ─────────────────  ─────────────────────────
Route-C      ∀ρ≠1/2 no off-line zero        detector ✓ proved   canonical Weil ≤ 0 (sign, axiom)
Gate-3U      canonicalRealGate3UAt (∥≤1∥)   unit HS ✓          generic-λ HS, cross-branch =0
             (cross-branch =0 is dangling)                      (838-gap + no =0 theorem)
```

Both open inputs are prop/statement axioms for the SAME endpoint / half-density sign,
wrapped twice. Consequences:

- **Don't chase both routes in parallel.** Both currently chase a canonical-nonpositive
  which the concrete space refutes (detector-positive vs canonical>≤0 are the same sign
  with flipped targets). The honest move is to ask whether that endpoint half-density
  sign is really `≤ 0` at all.
- If the concrete test already yields positive `weilLocalSum`, then the `canonical ≤ 0`
  premise (the Route-C open axiom) is **false for that space** — so task (1)'s "open"
  is a fake problem on this very space; the correct RH cannot rest on asserting
  `canonical ≤ 0`. It must rest on showing the half-density sign differently.

How (3 steps):

1. **Formally decide the canonical sign on this space as the foundation.**
   `not_normalizedCC20FiniteVanishingWeilCriterion` (2474) already proves the
   concrete space does NOT satisfy the canonical criterion. So "a clean carrier whose
   canonical sum is ≤ 0" is not this space — it needs (a) a different test space, or
   (b) a reworded criterion tolerating endpoint zeros. That is the real new analysis.
2. **If you still go Gate-3U, do NOT open with "build generic-λ HS".** Even with
   `Summable ‖…‖` you only get a ∥ ≤ bound∥ gate; the `= 0` (RH-level) cross-branch
   cancellation still needs the exact half-density R0 arithmetic. Prefer making the
   half-density endpoint sign a first-class theorem (at least: if the half-density sum
   mixes signs, then it has a well-defined zero) instead of stacking on Summable.
3. **Honest ceiling.** Both routes are resting on a one-dimensional sign decision
   (half-density pole ± ). Real RH needs either "positive canonical (proved, not
   assumed)" or "the half-density difference = const > 0 is impossible" — an analytic
   / arithmetic input, all the Lean plumbing (detector ✓, HS ✓, gate criteria
   ✓) is done. The missing line is that single base sign, which is prime mathematics,
   not re-piping an axiom.

## Repro

```
# No new probe; build-verify existing modules (WSL):
lake build ConnesWeilRH.Source.CC20YoshidaConstruction
lake build ConnesWeilRH.Route.CC20RouteRealization
# #print axioms normalizedCC20YoshidaDetectorExists = [propext, Classical.choice, Quot.sound]
```