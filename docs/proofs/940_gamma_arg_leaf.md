# 940 - Gamma-phase route: the arg(Gamma(1+i/2)) leaf is the whole remaining gate

Date: 2026-08-10. Status: inventory + exact-leaf pin. RH NOT claimed.

## 1. What is fully reduced (axiom-clean, verified this round)

Step-3 finite-S Weil sign on the Gamma-phase route has now been reduced to ONE
analytic leaf.  All algebraic wraps are theorem-closed:

  * `Dev/Finite3SignReduction.lean` (new, A1+A2+A3): `reFourth_nonneg_of_cone`
    proves `(0 < Re w) & (|Im w| <= (sqrt2-1) Re w) => 0 <= Re(w^4)`. Since
    `sqrt2-1 = tan(pi/8)`, the premise is exactly `|arg w| <= pi/8`.
  * `Dev/ArchPhaseZFourthNonneg.lean` (existing, axiom-free):
    `re_pow4_nonneg_of_abs_arg_lt_pi_eighth` gives the same from `|z.arg| < pi/8`.
  * `Dev/ArchPhaseWindow.lean` (existing, axiom-free): `gammaPhase_window` proves
    `0 <= Re[(Gamma(a+i/2))^4]  <->  (1/2 <= Re[Gamma/start]^2)` (cosine criterion).
  * `Dev/GammaImaginaryAxisModulus.lean` (existing, axiom-free): $|Gamma(1+i/2)|^2
    = pi/(2 sinh(pi/2)) $ (modulus is rigid).

So the four-function chain

   A3-cone  <=>  |arg w| <= pi/8  =>  0 <= Re[w^4]  <=>  cosine criterion

is closed. The arch gate `archPhaseGate a <-> 0 <= Re[(Gamma(a+i/2))^4]`
(`Dev/ArchPhaseSignSlot.lean`) only waits on the single analytic bound

   |arg Gamma(1+i/2)| <= pi/8          (= the concrete . `Gamma_arch_phase` leaf)

## 2. Why that is genuinely the open ANALYTIC (new-math) leaf

- mathlib v4.30.0 has NO complex-Gamma Stirling/asymptotic and NO `arg Gamma`
  bound (docs/869, /888).  `norm_num` cannot decide `Re[Gamma]` because Gamma is
  non-computable (defined via the Gamma Integral).
- Numeric anchor (high precision, docs/888): `arg Gamma(1+I/2) = -0.244058...`,
  interior to `[-pi/8, pi/8] = [-0.392699, 0.392699]` with margin ~0.148.
- The "official" analytic identity to formalize is the Weierstrass log-Gamma
  phase at the base point:
      arg Gamma(1+i/2) = -gamma/2 - atan(1/2) + S,   S in [1/2, 1/2 + 1/32].
  This is already analytic-level certified (docs/868, `SSeriesSandwich`/
  `PhaseGateSandwich`/`ArctanCert` close `S` and `D = S - gamma/2 - atan(1/2)`
  axiom-free).  What is NOT in the repo is the *connection* between the real
  number `Complex.Gamma (1 + i/2)`'s argument and that elementary `D`; proving
  `(Gamma (1 + I/2)).arg = D` needs a self-contained Weierstrass/Gauss partial
  product argument for the Gamma in Lean - a genuine new-analysis formalization.

## 3. Route judgment

- Closing this one leaf does NOT by itself assert RH: it provides the input to
  the arch-phase gate, which is an input to the finite-S sign, which feeds the
  exit chain up to the RH-equivalent criterion `normalizedCoreCC20PropositionC1
  SourceCriterion` (UnconditionalSkeleton).  So the Gamma route gets us a true
  finite-S `Re[Gamma^4] >= 0`, but the hard bottom stays the RH-equivalent C1.
- The canonical/CompactLog A3 + `detector_diagonal_re_nonneg` PSD route is the
  sibling the project already wires into `routeFullPositivityToQWNonnegative`;
  it does not need the Gamma argument at all (docs/869).

## Next
Either (a) attack `(Gamma (1+I/2)).arg` via a self-contained Weierstrass/Stirling
in-repo real-analysis proof (long, multi-session), or (b) push the canonical
CompactLog/A3 non-empty `fullWellPositivity` branch. Both stop before the
RH-equivalent Criterion.




## 4. Same-turn route verification: CC20 finite-vanishing producer is REJECTED

`Route/CC20RouteRealization.lean:54-70` already proves axiom-clean that the finite-
vanishing CC20 input has EMPTY `fullWeilPositivity`:
  `not_normalizedCC20FiniteVanishingWeilCriterionInput_fullWeilPositivity :
    normalizedCC20FiniteVanishingWeilCriterionInput.fullWeilPositivity -> False`
(via `CC20YoshidaInterpolationNode.not_normalizedCC20FiniteVanishingWeilCriterion`).
So the "canonical" route cannot get `Nonempty input.fullWeilPositivity` on the
CC20 finite-vanishing carrier: it is a documented rejection boundary, not a producer.

Consequence: of the two routes that look close,
  (i) CC20 finite-criterion `fullWeilPositivity` is falsifiable (provably empty);
  (ii) the Gamma-phase Argument `|arg Gamma(1+i/2)| <= pi/8` is the ONE genuinely
       open (new-math) leaf, but closing it only supplies an input; the exit
       `normalizedCC20PropositionC1SourceCriterion` remains RH-EQUIVALENT.
So both doors stop at (or reproduce) the RH-equivalent C1 criterion.


## 5. Axiom-clean hinge module (verified this turn)

`Dev/GammaArgLeaf.lean` (new, axiom-clean, 0 sorry) makes the reduction AIRTIGHT:
`gammaSign_at_one (harg) : 0 <= Re[(Gamma(1+i/2))^4]` with
`harg : |(Gamma (1 + i/2)).arg| < pi/8`.
That is, the whole a=1 finite-S arch sign is now one theorem one premise away from
a closed constant. The premise IS THE analytic leaf (Weierstrass/Stirling) listed
in docs/888 §3 / 869: build an in-repo real-analysis Gamma-argument bound at 1+i/2.
After that, finish: gammaSign_at_one -> archPhaseGate (ArchPhaseWindow) -> finite-S
sign. Still no RH: the exit is RH-equivalent.

