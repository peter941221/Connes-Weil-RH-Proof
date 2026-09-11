# Record 1327 — G8 P1 column energy alignment

**Status:** LANDED. Verification batch
`1540_g8_p1_column_energy_alignment_batch.log` (2138 lines, **3488 jobs**,
0 `error:`, 0 `sorryAx`, 8/8 `#print axioms` exactly
`[propext, Classical.choice, Quot.sound]`).

**Owner leaf:** `ConnesWeilRH/Dev/C1G8P1ColumnEnergyAlignment.lean`
**Audit leaf:** `ConnesWeilRH/Dev/C1G8P1ColumnEnergyAlignmentAudit.lean`

## What problem this record closes

After 1324-1326 both P1 boundary channels were known to eat the *same*
composite input, up to the two closed channel constants:

```text
metric side  (1326):  √q_p      × ‖antiresonantColumn(newFrame†(oldFrame x))‖
radial side  (1325):  32 ‖q_p⁻¹‖ × ‖antiresonantColumn(newFrame† u)‖
```

The radial energy transport (1324) turned the full-carrier column-energy
summability premise into the radial crossing basis energy. What was
missing was the **metric-side counterpart**: the same premise had not
been connected to the metric boundary composite

```text
B(p,S) = antiresonantColumn ∘L newFrame† ∘L oldFrame
```

along an arbitrary *source* basis. Record 1327 closes exactly that gap,
so that both channels now consume ONE named analytic input.

## Contents

| # | Declaration | Kind | Statement |
|---|-------------|------|-----------|
| 1 | `summable_comp_normSq_of_contractive_pull` | theorem (generic) | HS summability survives precomposition with a contraction: from `Summable ‖C u_i‖²` and `‖pull‖ ≤ 1` conclude `Summable ‖(C∘pull) b_j‖²` on any source basis |
| 2 | `summable_metricBoundaryComposite_normSq_of_fullCarrierColumnEnergy` | theorem | the full-carrier column premise implies `Summable fun j => ‖B b_j‖²` along any source basis |
| 3 | `norm_radialSoninBoundaryCrossing_apply_oldSuffixFrame_le` | theorem | same-input radial ledger at `u := oldFrame x`: `‖radial(oldFrame x)‖ ≤ 32 ‖q_p⁻¹‖ ‖B x‖` |
| 4 | `summable_radialCrossingAfterOldFrame_normSq_of_fullCarrierColumnEnergy` | theorem | `∑_j ‖radial(oldFrame b_j)‖² < ∞` from the same premise |
| 5 | `metricBoundaryColumnEnergyOperator` | def | the positive boundary energy operator `B† B : source →L source` |
| 6 | `metricBoundaryCauchyPairData` | def | explicit owning pair `BasisHilbertSchmidtPairData` with equal legs `B` |
| 7 | `metricBoundaryCauchyPairData_traceProduct_eq_energyOperator` | theorem | pair trace product is exactly `B† B` (`rfl`) |
| 8 | `metricBoundaryColumnEnergyOperator_isTraceClassAlong` | theorem | `B† B` is trace-class along the source basis, conditional on the premise |

## Why the generic engine is two lines

HS∘contraction is classical, but the repo only had the adjoint direction
(`summable_adjoint_normSq`). The trick: apply that theorem **twice** and
never touch a Fubini exchange directly.

```text
step 1  C HS along {u_i}  ⟹  C† HS along {u_i}      (first application)
step 2  ‖(C∘pull)† u‖ = ‖pull†(C† u)‖ ≤ ‖pull‖·‖C† u‖ ≤ ‖C† u‖
        ⟹ (C∘pull)† HS along {u_i}                  (domination)
step 3  (C∘pull)† HS along {u_i}  ⟹  (C∘pull) HS along {b_j}
                                                    (second application,
                                                     any target basis)
```

Step 3 also exploits that `summable_adjoint_normSq` reads its output on
an *arbitrary* target basis — so the source basis `{b_j}` never needs to
relate to the carrier basis `{u_i}` at all.

## Honest non-claims

* The full-carrier column-energy premise is **not proved** here; it
  remains the shared analytic input carried open by 1324 (and is the
  RH-level content of P1).
* No vanishing of any column energy, no sign, and no RH-facing claim.
* No metric-to-radial cutoff identification beyond the same-input
  ledger of theorem 3.

## Build lessons banked

* `prefix` is a reserved Lean 4 command token (notation-declaration
  syntax); it cannot be a binder identifier — parse dies at the binder
  with `unexpected token 'prefix'; expected '_' or identifier` and
  everything downstream cascades.
* `CCM24FiniteSActualSchurCascade` declares `sourceSoninCarrier`'s
  `CompleteSpace` as a `local instance` — **`local` instances are not
  exported**. Every downstream file must re-declare the instance from
  `(ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe`.
* `summable_adjoint_normSq` lives one namespace deeper than expected:
  full path
  `...PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq`.
* Mathlib v4.30's `Summable.congr` is the direct form
  `Summable.congr (hf : Summable f) (hfg : ∀ b, f b = g b) : Summable g`
  — not an iff.
* Dot-notation `.adjoint` on a parenthesized `∘L` chain can get stuck on
  `SeminormedAddGroup ?m`; write `ContinuousLinearMap.adjoint (chain)`
  explicitly.
* `Summable.of_nonneg_of_le` pairs with `Summable.mul_left`: the
  multiplication constant must match the calc's square — use
  `(c)^2` in `mul_left` when the pointwise bound is `‖·‖² ≤ c²·‖·‖²`.
