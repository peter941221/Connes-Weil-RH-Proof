# 1415 — Campaign brick 4 is a PHANTOM: the dictionary identity was already landed; the F2 campaign closes with an empty queue

Wave: F2 formal campaign (brick 4 — closed by recon, zero new code).
Depends on: 1412, 1413, 1414 (bricks 1-3 GREEN), and the landed
center-two assembly machinery this record re-reads.
Status: **VERDICT RECORDED — no build, no digits (law 65: none needed).
RH is not claimed.**

+========================================================================+
| [1] VERDICT                                                             |
+========================================================================+

The 1412 plan listed brick 4 as "the dictionary `psi = classical Q` —
LONG, paper-scale." Prereg-phase recon (this record; read-only, law 42
applied to a formal brick as a statement-level prereg) found the
content ALREADY LANDED as an unconditional machine fact, with an
existing axiom probe:

  +------------------------------+--------------------------------------+
  | ingredient                   | where (all in ConnesWeilRH/Dev)  |
  +------------------------------+--------------------------------------+
  | the dictionary PROPOSITION   | C1SpectralWeil.lean:597-600        |
  | gate2ExplicitFormula F       | := SpectralSummable F AND          |
  |                              | C1SameOwnerWeil.psi F =            |
  |                              |   spectralWeilValue F              |
  +------------------------------+--------------------------------------+
  | summability leg, ALL tests   | C1SpectralSummability.lean:372-377 |
  | spectralSummable (F)         | via                                |
  |                              | spectralHeightMultiplicity_        |
  |                              | geometric_bound (q = 3)            |
  +------------------------------+--------------------------------------+
  | identity leg, UNCONDITIONAL  | C1XiCenterTwoArithmeticAssembly    |
  | centerTwo_arithmetic_eq_     | .lean:232-236, discharged from the |
  | spectral : psi F =           | PROVED half-anchor Gauss formula   |
  | spectralWeilValue F          | via centerTwoGammaReadbackContract |
  |                              | _of_halfAnchorGauss                |
  +------------------------------+--------------------------------------+
  | full proposition, ALL tests  | C1XiCenterTwoArithmeticAssembly    |
  | gate2ExplicitFormula_        | .lean:240-244                      |
  | centerTwo (F)                |                                    |
  +------------------------------+--------------------------------------+
  | wall consumption             | C1CenterTwoCriterionBridge.lean    |
  | qw g =                       | :28-32 (rw [qw_eq_psi_square];     |
  | spectralWeilValue gSq        | exact centerTwo_arithmetic_eq_     |
  |                                spectral) — consumed by       |
  |                              | weilCriterion_iff_sourceRH at      |
  |                              | C1WeilCriterionEquivalence.lean:136|
  +------------------------------+--------------------------------------+

Fresh axiom evidence (this record, direct re-run of the existing
probe `C1XiCenterTwoArithmeticAssemblyProbe.lean`): all FOUR printed
declarations (`..._of_gamma_contract`, `gate2ExplicitFormula_of_...`,
`centerTwo_arithmetic_eq_spectral`, `gate2ExplicitFormula_centerTwo`)
print exactly `[propext, Classical.choice, Quot.sound]` — 4/4,
verified line-by-line (propext / Classical.choice / Quot.sound each
appearing in all four prints), no `sorryAx`.

+========================================================================+
| [2] WHAT IT MEANS FOR THE CAMPAIGN                                      |
+========================================================================+

The F2 campaign's four-brick plan was:

  brick 1  odd-annihilation            -> 1412 GREEN  (9 decls)
  brick 2  psi additivity              -> 1413 GREEN  (23 decls)
  brick 3  reflection invariance       -> 1414 GREEN  (19 decls)
  brick 4  dictionary psi = Q          -> THIS RECORD: phantom,
                                          landed by the center-two
                                          wave at register level

Total real campaign product: 51 new declarations, all standard-axiom,
all sign-free. Brick 4's cost was saved by obeying law F15 (price
before writing) at the PREREG stage: the recon took minutes; the
mispriced brick would have taken days duplicating landed theorems.

Diagnosis of the mispricing: law F8 (recon the register first)
RECURRING at campaign-planning scale. The 1412/1413 plan inherited
"brick 4 = LONG" from the 1411 fork framing ("dictionary psi=Q in
Lean"), which itself was written when the register's center-two
dictionary leg had not been re-read. F15 prices a campaign from the
exit's hypotheses; F8 says go READ them. This record closes that loop.

+========================================================================+
| [3] THE HONEST BOUNDARY: WHICH DICTIONARY IS MACHINE FACT               |
+========================================================================+

Two distinct claims were conflated by the word "dictionary":

  (a) INTERNAL DICTIONARY (formal, LANDED): `psi F` — the test-side
      arithmetic functional (pole minus archimedean minus primes,
      C1SameOwnerWeil) — equals `spectralWeilValue F` — the
      zero-side sum `re Σ_ρ spectralTerm F ρ` — for EVERY test,
      unconditionally. This is `centerTwo_arithmetic_eq_spectral`,
      machine-checked with standard axioms. The wall itself consumes
      it.

  (b) EXTERNAL DICTIONARY (model, NEVER a Lean Prop): that OUR
      formal `spectralWeilValue` is the PAPER'S classical Q of
      Yoshida/Chuk §2 with the same normalization and sign. This is
      a definitions-citation claim: 1407 (even cells) and 1410 (odd
      cell) measured PLUS_ONE agreement numerically (law 65: MODEL
      level), and 1408/1418 pinned the premises verbatim. No Lean
      statement of (b) is needed or possible without importing the
      paper as a formal source.

Cross-validation bonus: the landed machine identity (a) is exactly
what the MODEL measurements (1407/1410 psi-vs-Q cells) were probing
from the numeric side — the register's own identity and the rig's
double-evaluation agree, which strengthens both.

Kill (a) end-to-end status, machine level:
  odd tests annihilated [1412] + sums split [1413] + reflection-
  invariant [1414] + psi = zero-spectral value [landed] — the psi
  side of the 1405-1411 Chuk triangle is now FULLY formal. What
  stays outside the machine: the paper's positivity certificates
  (windows <= 0.8) and the wall `B0b` (the classical criterion, full
  quantifiers) — 1408's radius-disjointness conclusion is unchanged
  and unchanged in kind.

+========================================================================+
| [4] CAMPAIGN STATE AFTER 1415                                           |
+========================================================================+

  - F2 formal bridge campaign: CLOSED, queue empty.
  - Rig/paper queue: empty since 1411 (by mathematical necessity).
  - The only remaining known faces toward RH:
      (i)  the wall itself — rung 5, classical Weil criterion =
           RH normal form: a proof idea, not a campaign (Peter's
           decision, law F3 of the fork framing);
      (ii) importing the external certificates into Lean to
           strengthen the REGISTER narrative only: bounded work
           already assessed in 1406/1408 as consuming nothing the
           chain can use (radius disjointness), NOT queued.
  - Nothing in this wave claims RH, proves a sign, or moves a
    `sorry` in the mainline tower.

+========================================================================+
| [5] REGISTER DELTAS AND NEXT STEPS                                      |
+========================================================================+

  1. This record + README item 41; F8 recurrence noted in the
     conventions file.
  2. Commit + push (campaign closure bookkeeping).
  3. Frontier state: mainline register unchanged
     (tower -> gate `0 <= qw` <-> SourceRH via B0b; gate open);
     campaign artifacts now total 7 Dev leaves (1412-1414 trio +
     audits) plus this closure verdict.
  4. Default next action: hold (F1 freeze per 1411/1415), since
     every executable face is spent and what remains is the
     millennium-scale face itself.

RH not claimed.
