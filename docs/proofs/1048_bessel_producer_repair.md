# 1048 - The (gamma) Bessel producer repair: from 15 root errors to an accepted `hT`

Date: 2026-08-29.  Follows 1047.  Records the repair of
`ConnesWeilRH/Dev/C1CC20GammaBesselCoercivity.lean`, which 1047 had left as
the RED research frontier (forced `gamma6` build, 15 root errors), and the
resulting GATE 1 status change.

Paper-scale correction, same date: this record originally treated the
condition `lam < 1` as compatible with the paper.  It is not.  CC20 reports
the exceptional scale near `lam = 1.05158 > 1`.  The Bessel theorem below is
accepted Lean mathematics only for a non-paper parameter branch; it does not
discharge paper-scale payload (gamma).  Proof 1050 is the superseding route
judgment.

## What is now accepted

The Bessel leaf builds with a forced re-elaboration: zero `error:` lines,
`Build completed successfully (3633 jobs)`, and the paired audit
`C1CC20GammaBesselCoercivityAudit` prints, for every public declaration,

    depends on axioms: [propext, Classical.choice, Quot.sound]

with zero `sorryAx`.  The flagship payload is

    cc20Eq115_gate1hT (lam) (hlam : 0 <= lam) (hlam1 : lam < 1)
      (gapData) (hε : gapData.epsilon2 <= 1 - lam) :
      defect(xi) + gapData.a * (ell xi)^2 >= gapData.epsilon2 * ‖xi‖^2

exhibited with `ell := 0`.  This is an accepted producer for the
equation-(119) table only under `lam < 1`.  Paper-scale payload (gamma)
remains OPEN because `1 - lam < 0` at the reported scale.  A certified
finite-section/Toeplitz enclosure, or an equivalent exact complement frame
bound plus exceptional-direction repair, is therefore required rather than
optional.  The accepted row-band sandwich (`C1CC20GammaCoercivity`) remains
the consumption engine for that stronger certificate.

`C1CC20GammaBesselProbe.lean` is deleted per its own header contract
("delete once the brick lands"); git history retains it.

## Repair ledger (root causes, six forced builds)

1. star/exp rewrite order: unfolding `cc20WindowFourierModeRaw` and
   `cc20FourierPhase` in one `simp only` starves `star_cc20FourierPhase`
   (the pattern is gone once the phase is unfolded).  Apply the star lemma
   by `rw` FIRST, unfold afterwards.
2. `integral_indicator` is ambiguous under `open MeasureTheory` +
   `open intervalIntegral`: qualify `MeasureTheory.integral_indicator`.
   The whole-space -> set-integral direction is the one needed after
   folding the Gram integrand into a window indicator.
3. ite-condition ORDER must match the goal: `window_exp_integral (k - m)`
   yields `if k - m = 0 ...` while the theorem statement carries
   `if m = k ...`.  Bridge with `if_pos h.symm` / `if_neg (Ne.symm h)`,
   not `if_pos h`.
4. `rw` folds only the FIRST matched occurrence class.  A single
   `← Complex.ofReal_pow` normalizes one side's `(↑x)^n`; the second side
   needs the item repeated.
5. v4.30 elaboration of ascribed powers: `(e : ℂ)` + `^ 2` elaborates as
   `(↑e) ^ 2` — the power sits OUTSIDE the cast.  Every cast-fold
   (`← ofReal_mul`, `← ofReal_sub`, `← ofReal_sum`) must be preceded by
   `← Complex.ofReal_pow`, or `simp only` reports "no progress" although
   the goal looks like a pure product of casts.
6. `simp only [Complex.star_def, ...]` recursion-bombed in this state
   (star/conj loop).  The line was redundant once the rw chain carries
   `starRingEnd_apply` at the point of use; `Complex.norm_conj` clears a
   conj under a norm (`‖conj z‖ = ‖z‖`).
7. `sum_inner` = sum in the LEFT slot; `inner_sum` = sum in the RIGHT
   slot.  Near-anagram names; read the bodies, not the names.
8. CLM sum application `(∑ i, F i) ξ = ∑ i, F i ξ`: term-level `rfl`
   (`show ... from rfl`) fails with a type mismatch and `simp` makes no
   progress; the supported rewrite is `ContinuousLinearMap.sum_apply`.
9. omega atom discipline: after `cases`/`Prod.ext` the goal carries
   projection atoms `((an, false)).1` which omega does NOT unify with the
   hypothesis's `an`.  Pre-derive `have hn : (an.val : ℤ) = (bn.val : ℤ)
   := by omega` on plain atoms, then transport with `Int.ofNat_inj.mp hn`
   and let defeq eat the projection.
10. Bool `cases` order is false-then-true: the four subcases of
    `cases ab <;> cases bb` are (false,false), (false,true), (true,false),
    (true,true).  Bullets must follow that order.

## Build evidence

| Target | Evidence | Status |
| --- | --- | --- |
| `C1CC20GammaBesselCoercivity` + audit | Forced re-elaboration, zero `error:`, `Build completed successfully (3633 jobs)`; every audit declaration prints `[propext, Classical.choice, Quot.sound]`; `sorryAx` count 0. | ACCEPTED |

## GATE 1 status after this repair

| # | Payload | Status |
| --- | --- | --- |
| alpha | endpoint enclosure `hchi` | OPEN - interval-arithmetic ODE certificates |
| beta | joint (chi - tau) uniform-grid table | OPEN - blocked by alpha |
| gamma | paper-scale flagship `hT` | OPEN; Bessel is accepted only for the non-paper branch `lam < 1` |
| delta | archimedean comparison | OPEN - pinned to the CC20 §6 root window |
| gapData | paper-scale repaired-form data | OPEN; the Bessel exhibit applies only when `lam < 1` |

RH is not claimed.  Filling (alpha), (beta), paper-scale (gamma), (delta),
and the repaired-form data closes GATE 1 at the single entry point
`cc20Eq115_gate1Residual_nonpositive_of_uniformGrid`.

## Next steps

1. Build the paper-scale exceptional-direction/complement spectral
   certificate at `lam > 1`; do not reuse the Bessel exhibit.
2. (delta) transcribe the CC20 section 5-6 trace comparison on the same owner.
3. (alpha) build the interval-ODE certificate project, which unblocks beta.
