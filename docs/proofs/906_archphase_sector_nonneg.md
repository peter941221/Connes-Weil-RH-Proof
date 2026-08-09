# 906 - Arch-phase 4th-power nonneg sector lemma: Lean CLOSED (axiom-clean)

Date: 2026-08-08. Status: **Closed in Lean**, axiom-clean. Source:
`ConnesWeilRH/Dev/ArchPhaseZFourthNonneg.lean`.
This realises the generic polar/DeMoivre sub-lemma tracked in `docs/proofs/904`.

## What is proven

```lean
re_pow4_nonneg_of_abs_arg_lt_pi_eighth
    {z : ℂ} (hz : z ≠ 0) (h : |z.arg| < Real.pi / 8) : 0 ≤ (z ^ 4).re
```

with supporting lemmas

```lean
z_pow4_eq_norm_pow4_mul_exp (z) : z ^ 4 = (‖z‖:ℂ)^4 * Complex.exp (((4*z.arg):ℝ)*I)
re_z_pow4_eq_norm_pow4_mul_cos (z) : (z^4).re = ‖z‖^4 * Real.cos (4*z.arg)
re_pow4_pos_of_abs_arg_lt_pi_eighth (z) (hz) (h) : 0 < (z^4).re
```

Numerically true for the arch value: Re[Gamma(1+I/2)^4] = +0.26097 > 0.

## Proof route (one paragraph)

1. `Complex.norm_mul_exp_arg_mul_I z` gives the polar form `z = ‖z‖·exp(arg z·I)`.
   The 4th power is `‖z‖^4 · exp(((4*z.arg):ℝ)·I)` via `mul_pow`,
   `Complex.exp_nat_mul`, `Complex.ofReal_pow`.
2. The real part collapses: `Complex.mul_re`, `Complex.ofReal_re/im`, and
   `Complex.exp_ofReal_mul_I_re/im` give
   `(z^4).re = ‖z‖^4 · cos(4·z.arg)`.
3. `|z.arg| < π/8` implies `|4·z.arg| < π/2` (via `abs_mul`, `mul_lt_mul_of_pos_left`,
   and `4·(π/8)=π/2` by ring), so `Real.cos_pos_of_mem_Ioo` gives `0 < cos(4·z.arg)`.
4. `z≠0` gives `0 < ‖z‖` (`norm_pos_iff`), so `0 < ‖z‖^4`; `mul_pos` gives `0 < (z^4).re`,
   and `le_of_lt` gives nonneg.

## Axiom audit

`#print axioms` on all four declarations = `[propext, Classical.choice, Quot.sound]`;
0 `sorry`, 0 project axiom.

## Lean gotchas fixed during the build

- `rw [← Complex.norm_mul_exp_arg_mul_I z]` rewrites the `z` that appears in the
  RHS's `‖z‖`/`z.arg` too; force rewrite only the top-level `z` with `conv_lhs`.
- `Complex.exp (((4*z.arg):ℝ)*I)`: the argument must be typed `ℝ` then coerced, so
  `Complex.exp_ofReal_mul_I_re/im` (pattern `(exp(↑x*I)`.re/im) match; a plain `ℂ`
  `(↑z.arg)*4` term does *not* unify with the `ℝ`-coercing lemma.
- `4·(π/8) = π/2` needs `ring`/`ring_nf` (symbolic `π`), not `norm_num`.
- The nonneg theorem must take `hz : z ≠ 0` (a Prop), not `z != 0` (which is
  `Bool` level); pass through to the strict-positive theorem.

## What this closes / what stays open

- Closes: Lane-A's operator-side arch-phase **sign** piece
  `Re[Gamma(1+i/2)^4] >= 0` modulo the (separately open) Gamma magnitude identity
  `arg Gamma(1+i/2) = -gamma/2 + tsum S2` (docs/903) and its Lean logging product
  form. It is the `0<=Re(z^4)` sector fact `docs/904` asked for.
- Still open: the scalar (Field) Gamma magnitude identity itself (Lane-A heavy step,
  docs/901/902/903); wiring the HS gate at `RouteTheorem:1332`
  (docs/905 §8); and Lanes B/R do not claim RH.

RH is not claimed.

## Post-closure routing check (same day): this leaf is NOT on the RouteTheorem gate

After closing 906, wiring it into `RouteTheorem.lean:1332` was attempted. The
route check is decisive and negative:

- `RouteTheorem.lean:1332` consumes `sourceTrace.hilbertSchmidtGate` where
  `SourceTraceScaleData.hilbertSchmidtGate g = traceClass g ∧ cyclicLegal g`
  (AnalyticCore.lean:8140-8144). It is a trace-LEGALITY gate, not a sign gate.
- The actual archimedean sign on that path is `archimedeanSignNormalized`
  (a row of `SignsAndNormalizationsStatement`), already closed axiom-clean via
  `HilbertCarrierReTypedSymbols.archimedeanSignNormalized :=
  Nonempty HilbertSignArchCorrected.HilbertArchSignDatum`, where the datum's
  `operator_psd` is `windowedBoundaryDetector test a c` being positive = `F† F`
  (HS quadratic form `‖F u‖² ≥ 0`), NOT `Re[Gamma(1+I/2)^4]`.
- The route's archimedean HS gate (`hilbertSchmidtGate`) is supplied by the
  concrete `cc20Trace` model via `SourceTraceReadOffData`; the Hilbert-carrier
  closure (`Dev/HilbertTraceModelClosure`, `HilbertCarrierReTypedSymbols`) is a
  `Dev/` artifact NOT imported into `UnconditionalSkeleton` / `RouteTheorem`.
- No `Gamma`, no `arg Γ`, no `Re[...^4]`, no `π/8` appears anywhere under
  `Route/` or `Basic.lean`.  The whole `Re[Gamma(1+I/2)^4]>=0` / `|arg| < π/8`
  line lives only in `Dev/` and docs (901/902/903/904/906).

Conclusion: the 906 sector lemma is a correct, axiom-clean, numeric-validated
leaf, but it is NOT a real dependency of `RouteTheorem:1332`'s gate. The
`Re[Gamma(1+I/2)^4]` route has no consumer in the actual RH pathway yet. The
routes that DO move RH on the gate side are instead:
  (H1) wire `HilbertTraceModelClosure.retypedTraceModel` (Hilbert carrier:
       `Gate_nonempty`, `scalarTrace=sq_norm>=0`, `F†F`-PSD sign) into the
       skeleton's `sourceObject.cc20Trace` — a model re-point (architecture,
       needs Peter);
  (H2) Lane-B: re-type the broken concrete `SourceWeilFormData` / finite-prime /
       convolution model so the skeleton no longer bottoms on those `axiom`s.
Neither H1 nor H2 needs the 906 `Re[Gamma^4]` leaf.
