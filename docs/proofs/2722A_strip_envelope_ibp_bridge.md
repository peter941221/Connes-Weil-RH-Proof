# Record 2722A: the integration-by-parts bridge turns the three wired
strip envelopes into consequences of scalar derivative-ladder pins

## Verdict

GREEN (mechanism). The module
`ConnesWeilRH/Dev/C1StripEnvelopeIbpBridge2722.lean` proves the generic
integration-by-parts (IBP) bridge for `laplaceAt` on the
`CompactLogTest` owners and packages it in exactly the statement shape
of the three wired strip-envelope hypotheses
`hcontract / hquartic / hquadratic` of
`fourPointContradictionRowBWired2721C` (record 2721). Acceptance:
Linux-native focused audit build green, footer
`Build completed successfully (3644 jobs)`, zero `error:` lines, zero
`sorryAx`, zero warnings on the new module, and all nine public
declarations depend on exactly `[propext, Classical.choice, Quot.sound]`
(`results/2722a_axiom_census.json`, Windows/Linux md5 parity
`c219afaf167f9ad14456dd45e9e5df33` / `09f0da9f6dea033ccb79129128e63d68`).

No wired hypothesis is removed by this run. The bridge converts each
quantified functional premise into (i) a support fact and (ii) ONE
explicit scalar inequality on the `derivOrderL1` ladder, so the residual
obligation is strictly smaller and finitely checkable: three forall
strips become three named pins plus the concrete-owner support facts.
The pins are still hypotheses (proxy-tie doctrine of records 2657 /
2721B): the Lean statements consume named constants, and the numeric tie
to the certified record-2720 constants is an artifact-side checker duty
in the next rung.

## What it is

The consumer chain (record 2355 seam, record 2721 wiring) takes the
strip envelopes as black-box assumptions on generic owners:

```
(hcontract : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
  64 ≤ |t| →
    ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
      wiredQRowB2721)
(hquartic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
  ‖t / (2 * Real.pi)‖ ^ 4 *
    ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
      wiredC4RowB2721)
(hquadratic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
  ‖t / (2 * Real.pi)‖ ^ 2 *
    ‖laplaceAt correction ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
      wiredC2RowB2721)
```

This record proves that all three shapes follow from the classical
Laplace-side IBP identity, iterated:

- `laplaceAt_derivativeShift` (committed, `C1CompactSupportLaplaceBounds`):
  `laplaceAt (derivativeShift f 0) s = (0 - s) * laplaceAt f s`, so each
  shift multiplies the transform by `‖s‖` at the price of one more
  derivative.
- `norm_laplaceAt_le_exp_mul_l1Mass` (committed): the order-zero anchor,
  `‖laplaceAt f s‖ ≤ exp (|s.re| * B) * derivOrderL1 0 f` under
  `Function.support f.test ⊆ Set.Icc (-B) B`.
- `derivOrderL1_shift_zero` (proved here):
  `derivOrderL1 n (derivativeShift f 0) = derivOrderL1 (n + 1) f`, the
  ladder bookkeeping step, from `iteratedDeriv_derivativeShift_apply`.
- `derivativeShiftZero_support_subset` (proved here): the zero shift
  keeps the support inside the same interval, via
  `support_deriv_subset` and the closed-hull transfer
  `tsupport f = closure (support f) ⊆ Icc`.

The induction gives the bridge theorem

```
norm_pow_laplaceAt_le_exp_mul_derivOrderL1 :
  ∀ (k : ℕ) (f : CompactLogTest) (B : ℝ),
    Function.support f.test ⊆ Set.Icc (-B) B →
    ∀ s : ℂ, ‖(s : ℂ)‖ ^ k * ‖laplaceAt f s‖ ≤
      Real.exp (|s.re| * B) * derivOrderL1 k f
```

and two corollaries that match the wired shapes verbatim:

- `wiredStripDecayOfLadderPin (f) (B C) (k) (hB) (hsupport)
  (hpin : Real.exp B * derivOrderL1 k f ≤ C)` gives the weighted-power
  forall strip — `hquartic` at `k = 4` for `base`, `hquadratic` at
  `k = 2` for `correction`.
- `wiredContractOfDecayPin (f) (B T q) (k) (hB) (hT : 0 < T)
  (hsupport) (hpin : Real.exp B * derivOrderL1 k f ≤ q * T ^ k)` gives
  the threshold form — `hcontract` at `T = 64`, `q = wiredQRowB2721`,
  at any ladder order `k`.

The strip-point geometry is carried by three small proved helpers:
`im_ofReal_add_mul_I`, `re_ofReal_add_mul_I`,
`abs_le_norm_ofReal_add_mul_I` (height dominated by modulus), plus
`exp_weight_le_exp` (on `sigma ∈ [0, 1]` the weight `exp (|s.re| * B)`
is at most `exp B`) and `one_le_two_pi` (private, from
`Real.pi_gt_three`).

## Why it is the right decomposition

+---------------------------------------------------------------+
|  wired premise (quantified over the whole strip)              |
|                                                               |
|  forall sigma in [0,1], forall t:  ‖t/2π‖^k ‖laplaceAt f z‖ ≤ C|
+------------------------------^--------------------------------+
                               |  proved here, twice
+------------------------------+--------------------------------+
|  ONE scalar pin              |  support fact                  |
|  exp B * derivOrderL1 k f ≤ C|  support f.test ⊆ [-B, B]      |
+------------------------------+--------------------------------+

The two reductions differ in one structural respect that matters for
the next rung: the decay pins (`k = 4`, `k = 2`) are strip-uniform and
direct, while the contraction premise is converted at an ARBITRARY
ladder order `k` — it holds whenever `exp B * derivOrderL1 k f ≤ q * 64^k`
for some `k`, so the order is a free parameter of the discharge, and the
2720 certified ladder table `D_1..D_12` can be searched for the first
order that closes. This is exactly the arithmetic that record 2720
measured in the pipeline convention and that record 2354's scalar
acceptance lanes priced at `T = 128` for the other family; the Lean
side has never been given a chance to check it order by order.

Honest scope: the bridge proves no numeric fact. The pins `C`, `q`, `k`,
`B` and the ladder values are hypotheses; the owners are generic
`CompactLogTest`. Identifying `laplaceAt base / laplaceAt correction`
with the record-2720 pipeline cardinal is the registered P2/seam duty
and stays open.

## Acceptance evidence

- Build: `LEAN_NUM_THREADS=1 lake build
  ConnesWeilRH.Dev.C1StripEnvelopeIbpBridge2722Audit` on the Linux
  native workspace; footer `Build completed successfully (3644 jobs)`.
- Census: `results/2722a_axiom_census.json` — `error_lines: 0`,
  `sorryAx_lines: 0`, `uses_sorry_lines: 0`,
  `warnings_on_new_module: 0`, `record_count: 9`, `all_trio: true`,
  `parity: true`.
- Declarations (public, nine): `derivativeShiftZero_support_subset`,
  `derivOrderL1_shift_zero`,
  `norm_pow_laplaceAt_le_exp_mul_derivOrderL1`, `im_ofReal_add_mul_I`,
  `re_ofReal_add_mul_I`, `abs_le_norm_ofReal_add_mul_I`,
  `exp_weight_le_exp`, `wiredStripDecayOfLadderPin`,
  `wiredContractOfDecayPin`.

Fix cycle (four builds, all defects inside the new module): a dead
`exact` after a `rw` that already closed the goal via the `@[refl]`
attribute; `Real.pi_gt_three` living in
`Mathlib.Analysis.Real.Pi.Bounds` (the trigonometric-bounds import does
not expose it); the deleted v4.30 name `div_le_div_right` and the
`div_self` mis-application replaced wholesale by a division-free
cancellation route (`le_of_mul_le_mul_left / _right` from the
`PosMulReflectLE` / `MulPosReflectLE` classes); a bare
`mul_comm X ^ k q` parsing as an application of `q` to `X ^ k` (parenthesized);
and `linter.style.show` goal-changing `show` replaced by `change`.

## Task card for the rungs this opens (2722B / 2722C)

- Owner: the row-B `(base, correction)` at `n = 3`, `N = 5` as captured
  by the 2721 wiring constants (`q = 26/10^17`, `C4 = 61000000`,
  `C2 = 29000000`, `T = 64`).
- Named premises to remove (one per rung): 2722B — the scalar pins as
  decidable numeric obligations: search the 2720 certified ladder for an
  order with `exp B * D_k ≤ q * 64^k` and orders 4/2 for the decay
  constants; a failing screen at every order is a named, reproducible
  no-go on the 2720 grade of constants. 2722C — the concrete support
  facts `Function.support base.test ⊆ Icc (-B) B` and the owner
  identification (P2/seam) of `laplaceAt base / correction` with the
  pipeline cardinal, clearing the 2ay slab guard from `storedWidth` data.
- Consumer: `fourPointContradictionRowBWired2721C` (the wired
  contradiction) via `selectedOwner_fullOrbit_span_fourthOrderSpectralTail_of_q`.
- Measurable completion per rung: a checked Lean instance of the bridge
  corollary at the concrete constants, or a recorded scoped no-go.
- Budget: one bounded screen script plus one focused build per rung; no
  grid expansion, no degree escalation without a named hypothesis change.
- Stop condition: if the 2720-grade ladder fails the contraction pin at
  every order up to the certified table's end, record the scoped no-go
  and freeze this lane; do not reopen map 103.

## Nonclaims

No wired hypothesis is discharged in this run; no numeric tie is
machine-checked yet; no gate sign, no prefix bound, no source-zero
completeness, no producer GO, no RH claim. The map-103 freeze is
unchanged.
