Record 2646: complex phase scalar engine GREEN + analytic containment bridge GREEN (2624 GO-route brick 1 landed)
Date: 2026-10-10

Result

Positive: two new modules built green and committed together.

1. `ConnesWeilRH/Dev/C1RouteAComplexPhaseEngine2646.lean` — the
complex phase scalar engine, brick 1 of the record-2624 GO route.
Core definition:

    def phaseExp2646 (phase : ℚ) (index : ℕ) : RatState2542 :=
      compactExp2620 (0, phase / (2 : ℚ) ^ index) index

Interface theorems (all proven, no sorry, no new axiom):

    embedPhase2646          embedPair2542 (0, phase / 2 ^ index)
                              = Complex.I * ↑(phase / 2 ^ index)
    phaseExp_small2646      ‖embed (0, phase / 2 ^ index)‖ ≤ 1/1000
    phaseExp_exp_error2646  ‖exp (I * phase) - embed (phaseExp ..).1‖
                              ≤ (phaseExp ..).2
    exp_I_re_cos2646        re (exp (I * t)) = cos t   (t : ℝ abstract)
    exp_I_im_sin2646        im (exp (I * t)) = sin t
    phaseExp_cos_error2646  |cos phase - ball.re| ≤ ball radius
    phaseExp_sin_error2646  |sin phase - ball.im| ≤ ball radius

The main theorem transports the certified 2620 replay error through
the `2 ^ index` reassociation: the reduced-argument ball equals
`exp(I * phase)` up to the SAME 400-bit radius the engine stored.
The cosine/sine interface theorems extract both coordinates against
that one shared radius — exactly the shape the degree-55 complex
panel tables multiply into their Horner chains.

2. `ConnesWeilRH/Dev/C1RouteAAnalyticContainmentBridge2646.lean` —
`socket_diagonal_split2646`: the full 30x30 containment premise of
the 2597 socket follows from the 870 off-diagonal memberships plus
the certified diagonal partition (record 2645). Proof is a
`rcases eq_or_ne i j` split: diagonal from
`actualOwnerMomentMatrix2351_diagonal_mem2645`, off-diagonal from the
hypothesis. This states the exact remaining obligation shape for the
off-diagonal campaign — nothing more.

Build evidence (log-verified, not exit codes):

    engine   Built 42 s first green (1.4 s incremental recheck),
             errors 0, `uses sorry` 0, module warnings 0
    bridge   Built green over a 20058-job graph, errors 0

Scope

The engine is a pure interface layer over the certified 2620 compact
engine: it introduces no numeric panels and no new axioms; axiom
status is inherited unchanged (the campaign axiom trio). No
off-diagonal membership is claimed by either module — the bridge
only names the off-diagonal side as a hypothesis. Producer GO,
SourceRH, and RH remain open and out of scope.

Pipeline notes (evidence-based debugging laws)

- simp? probe module: a throwaway `Probe2646.lean` with `simp?`
  produced the exact failing subterms in one 42 s build and settled
  two debates that three blind iterations had not. Probe was deleted
  from both sides after use and never committed.
- Cast-split law: on a DivisionRing target, simp's default set (and
  simp? suggestions) rewrite `Rat.cast (a / b)` via `Rat.cast_div`
  into a complex division, after which `Complex.ratCast_re` /
  `ratCast_im` can never match. Inside `Complex.ext` branches, use a
  curated `simp only` set that never splits the cast; eliminate the
  stuck projections arithmetically (`zero_mul`/`one_mul`).
- i-rotation arithmetic: `(I * w).re = -w.im`, not 0.
  `zero_sub` is `0 - a = -a` — it does not say `0 - a = 0`.
- Projection-outside-subtraction law: `rw [hcos] at hreal` into
  `|(exp .. - embed ..).re|` fails because the pattern `(exp ..).re`
  does not occur — `.re` sits on the subtraction. Distribute first
  with `Complex.sub_re` / `Complex.sub_im`, then the component
  rewrite fires verbatim.

Next obligations

1. Complex list helpers + complex residual stability theorem at
   degree 55 (2624 GO route steps 2-3), consuming phaseExp2646.
2. Off-diagonal pilot entry (0,3): generate the 190 complex panel
   tables with the 2622 batch machinery as template, then assemble
   the (0,3) containment against the committed 2597 rectangle.
3. Static consumer, Producer GO, SourceRH, RH remain open.
