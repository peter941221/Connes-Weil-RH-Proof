# Record 2671 - interval rectangle corner-norm bridge

**Verdict: FORMAL-SOUNDNESS-BRICK-PASS; producer gate remains open.**

The 2670 continuous-box price bounds a complex rectangle by taking the largest
absolute endpoint in each coordinate and applying square, addition, and square
root. This record formalizes that logical step in Lean.

The new definitions and theorems are in
`ConnesWeilRH/Dev/C1RouteAIntervalAlgebra.lean`:

- `ComplexRect2427.cornerNormSq` is the sum of the two coordinate-square
  bounds;
- `ComplexRect2427.cornerNorm` is its real square root;
- `ComplexRect2427.normSq_le_cornerNormSq` proves the rectangle contains the
  complex norm square;
- `ComplexRect2427.norm_le_cornerNorm` proves the norm bound used by the
  evaluator price.

The proof uses only the rectangle membership inequalities, the elementary real
square bound, `Complex.norm_def`, and monotonicity of `Real.sqrt`. The source
compiles in the active Linux Mathlib v4.30 environment with exit code 0. The
audited declarations use the project's standard axiom trio
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced.

This closes one evaluator-soundness sub-obligation. It does not prove the MPFR
directed-rounding implementation, the exact stored-width radius literal bridge,
the live-owner identity or coefficient-ball membership, the `chargeRest`
inequality, the signed infinite-xi tail, Producer GO, SourceRH, or RH.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAIntervalAlgebra.lean`
- `docs/proofs/2670_repaired_owner_continuous_box_price.md`
- `results/2670_repaired_owner_continuous_box_price.json`
