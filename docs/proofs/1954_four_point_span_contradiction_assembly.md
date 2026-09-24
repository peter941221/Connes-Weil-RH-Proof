# 1954 — Four-Point Same-Span Contradiction Assembly and Riemann Hypothesis Master Exit

Date: 2026-09-24

## Result

`ConnesWeilRH.Source.C1FourPointContradictionAssembly` formalizes Cut 3 of Map `103`,
assembling the two-sign contradiction on the same `annihilatorDetectorSpanVector` owner
and wiring the non-existence of right off-line zeros directly to Mathlib's
`_root_.RiemannHypothesis`:

1. `spectralWeilValue_neg_of_spectralHeightShellPrefix_and_tail_scaled`:
   Generalizes the shell prefix + tail negativity to an arbitrary positive bound `M > 0`:
   ```lean
   theorem spectralWeilValue_neg_of_spectralHeightShellPrefix_and_tail_scaled
       (F : CompactLogTest) (N : Nat) (M : Real)
       (hprefix : (∑ k ∈ Finset.range N, ∑' z : spectralHeightShell k, spectralTerm F z.1).re ≤ -M)
       (htail : (∑' m : Nat, ∑' z : spectralHeightShell (m + N), ‖spectralTerm F z.1‖) < M) :
       spectralWeilValue F < 0
   ```

2. `spectralWeilValue_neg_of_spectralHeightShellPrefix_and_fourthOrderTail_scaled`:
   Deduces `spectralWeilValue F < 0` from `FourthOrderSpectralTail` and a scaled prefix bound
   when the tail budget satisfies `4 * epsilon ^ 2 * spectralMultiplicityConstant * (3 / 4) ^ n0 < M`.

3. `qw_neg_of_spectralHeightShellPrefix_and_fourthOrderTail_scaled`:
   Transfers the spectral negativity to the same-owner Weil energy `qw v < 0` via the
   unconditional center-2 bridge `qw_eq_spectralWeilValue_centerTwo`.

4. `annihilatorDetectorSpanVector_qw_nonneg_of_gate`:
   Proves `0 ≤ qw (annihilatorDetectorSpanVector u g lam)` from Cut-2 gate nonpositivity
   (`orbitWindowSemiLocalGate`) and triple vanishing.

5. `false_of_qw_nonneg_and_neg` & `false_of_annihilatorDetectorSpanVector_gate_and_spectral_neg`:
   Forces `False` by `linarith` from the simultaneous nonnegativity `0 ≤ qw v` and strict
   negativity `qw v < 0` on the same test function.

6. `sourceRH_of_right_nontrivial_zeros_empty` & `riemannHypothesis_of_right_nontrivial_zeros_empty`:
   Connects the impossibility of right off-line zeros (`(1 / 2 : Real) < rho.1.re → False`)
   directly to `SourceRH` and Mathlib canonical `_root_.RiemannHypothesis`.

7. `riemannHypothesis_of_four_point_span_contradiction_producer`:
   Grand synthesis theorem: exhibiting for each hypothetical right zero a healthy detector owner
   whose four-point span simultaneously achieves gate nonpositivity and spectral negativity
   proves Mathlib canonical `_root_.RiemannHypothesis`.

## Verification

```text
Build completed successfully (3814 jobs).
axioms: [propext, Classical.choice, Quot.sound]
sorryAx: none
```
