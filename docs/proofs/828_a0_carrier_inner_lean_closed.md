# Route-C / A0: 828 — the nonzero carrier is proven axiom-cleanly in Lean (C2 + C3 closure)

Date: 2026-08-06 · Status: **formal Lean proof, axiom-clean.** The one analytic
input (A0) that C1/826 left open — existence of a nonzero carrier making the
crossing inner product genuinely nonzero — is now an exact, sorry-free Lean
theorem. RH stays conditional; this closes the A0 analytic parcel, not RH.
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/827_a0_positive_carrier_verdict.md`,
`docs/proofs/826_trace_class_gate_relaxation_design.md`,
`docs/proofs/825_prime_weight_renormalization_verdict.md`
EVIDENCE:
- `ConnesWeilRH/Dev/C2NonzeroCarrierProbe.lean` (committed)
- `ConnesWeilRH/Dev/C3NonzeroCarrierThrough.lean` (committed)
- under `ConnesWeilRH/Source/CC20Concrete/`: `GlobalLogHaar.lean`,
  `GlobalLogCrossing.lean`, `GlobalLogCrossingTraceClass.lean`, `PositiveTrace.lean`

## 0. Bottom line

The A0 witness asked for in 826/C1 — *a concrete carrier `k` on the crossing
space with `<k, SingleCrossing b k> ≠ 0`* — is now **proven** in Lean, not just
sampled numerically:

```
inner ℂ (stepCarrierLp b) (cc20SingleCrossingOperator b (stepCarrierLp b)) = b
0 < ( ... ).re        (when 0 < b)
```

The step carrier `k = 1_{[-b,b]}` is manufactured as an actual `L2` element
(`indicatorConstLp` of `Icc (-b) b` in `cc20GlobalLogCrossingL2 = Lp ℂ 2 volume`).
Both theorems depend only on `[propext, Classical.choice, Quot.sound]` — no
`sorry`, no `sorryAx` (verified with `#print axioms`). RH remains conditional.

## 1. Why this is the one analytic crack left open (recap of A0)

`826_trace_class_gate_relaxation_design.md` moved route C's Gate from an
operator-norm comparison (Proof 717 wall) to a trace-class carrier question.
`C1` proved the formal side already closes: the ordinary trace of the rank-one
smoothing `Tr(cc20SmoothedCrossing b k h) = <h, SingleCrossing b k>` (cyclicity,
axiom-clean) and `0 ≤ Tr(A†A)` is free. The single analytic input left open (A0)
was: **does a nonzero carrier `k` exist with `<k, SingleCrossing b k> ≠ 0`?**

827 showed numerically + trivially that `k = 1_{[-b,b]}` gives `= b > 0`, and
gave the explicit bridge. This doc 828 records the Lean proof of exactly that.

## 2. The two-module structure (C2 pointwise, C3 L2-through)

The proof splits cleanly along measure-theory vs. L2 plumbing:

```
C2 NonzeroCarrierProbe (pointwise / concrete)
   stepCarrierFn b t             : ℝ → ℂ    "1 if -b ≤ t ≤ b else 0"
   stepCarrierFn_in_window      : within [-b,b] the step = 1
   stepCarrierFn_out_of_window  : outside = 0
   stepCarrierFn_re_nonneg      : 0 ≤ (stepCarrierFn).re pointwise
   integrand_in_Icc_negB_zero   : on [-b,t ≤ 0], k(t)·k(t+b) = 1   <- analytic heart
   stepCarrierFn_ne_zero        : carrier is not the zero function (0 < b)

C3 NonzeroCarrierThrough (L2 / inner-product break)
   stepCarrierLp b : cc20GlobalLogCrossingL2 = indicatorConstLp 2 Icc(-b,b) 1
   stepCarrierLp_coeFn : its coeFn =ᵐ[volume] Icc(-b,b)-indicator
   integral_one_Icc_negb_zero : ∫_{-b}^0 1 = b
   stepCarrierLp_crossing_inner_eq   : inner = b            (THE result)
   stepCarrierLp_crossing_inner_pos   : 0 < (inner).re        (the A0 witness)
```

The bridge in C3:
- `L2.inner_def` turns the L2 inner product into a Lebesgue integral of the
  pointwise inner product.
- `cc20SingleCrossingOperator_coeFn_eq_Icc_indicator` rewrites the operator on
  `[-b, 0]` to `u(t+b)` (the crossing window identity).
- A `filter_upwards` ae-equal argument collapses the integrand to
  `1` on `Icc (-b) 0`, `0` outside.
- `integral_indicator` + `Real.volume_Icc` evaluate `∫_{-b}^0 1 = b`.
- `hb : 0 ≤ b` closes the last `simp` step.

## 3. Axiom audit (the deliverable)

```
#print axioms stepCarrierLp_crossing_inner_eq  => [propext, Classical.choice, Quot.sound]
#print axioms stepCarrierLp_crossing_inner_pos   => [propext, Classical.choice, Quot.sound]
#print axioms integrand_in_Icc_negB_zero        => [propext, Classical.choice, Quot.sound]
#print axioms stepCarrierFn_ne_zero             => [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `sorryAx`. The only dependencies are the standard Lean axioms
(`propext`, classical choice, quotients), so the A0 fact is genuinely derived,
not assumed.

## 4. Honest scope (what is and is not claimed)

- **Proven (exact, sorry-free):** a concrete nonzero carrier `k = 1_{[-b,b]}`
  realizes `<k, SingleCrossing b k> = b > 0`. This closes the A0 analytic
  parcel C1/826 named.
- **Proven (from library, exact):** the Gate scalar is the ordinary positive
  trace `Tr(cc20SmoothedCrossing b k k) = <h, SingleCrossing b k>`, already in
  `PositiveTrace` / C2's `trace_smoothedCrossing_eq_inner_const`.
- **NOT claimed:** RH. This route is conditional on the rest of the
  trace-class / commutator closure tying the Gate to the zero-corridor. The A0
  carrier now rests on a hard proof; it is no longer the open analytic input.
- **Deliberately not in this module:** a general `ordinaryTraceAlong`-equals-
  Lebesgue-integral equivalence for arbitrary L2 carriers, nor the
  full route-bottom-to-RH chain.

## 5. Repro

- Build: WSL native tree with warm cache (a couple minutes from the changed
  source). `lake build ConnesWeilRH.Dev.C3NonzeroCarrierThrough` passes
  (2956 jobs, only upstream warnings).
- Audit: `lake env lean` with `#print axioms` on the four theorems above.

## Handoff (route C)

- C1 formal trace-closure: done (axiom-clean) — committed.
- C2 pointwise step-carrier probe: done, committed.
- C3 L2 carrier-through proof: **new, done, axiom-clean, committed.** Closes the
  A0 analytic carrier-existence item end-to-end.
- RH: conditional, unchanged.

## Next steps

1. Tie C3's concrete inner product to the full `TrAlong` statement on a
   Hilbert-basis diagonal (the `ordinaryTraceAlong`-is-basis reduction), so the
   trace scalar `Tr = b > 0` is read off directly.
2. With the A0 carrier now a hard fact, re-examine route C's gate: the trace
   lane's closure condition is the remaining open item.
3. Update `826_...design.md`'s claim that "A0 carrier is numeric not formal" to
   "A0 carrier is now proven axiom-clean" (this module supersedes that
   sentence).