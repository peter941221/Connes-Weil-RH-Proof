# 1402 — Route-beta zero-digit recon: the beta campaign cannot breach the wall; it re-partitions it, and one piece IS the wall

Date: 2026-09-14. Pre-campaign reconnaissance for the surface that 1399 §8
and 1401 §4 named as the live lever after law F14 retired the route-alpha
grid: the root-supported even/odd (7-node) family. Zero digits computed:
no owner value, no anchor, no A of any kind. Every statement below is a
source readback with a file:line, or a quote of an already-committed
record. The recon question was the one 1401 promised to answer before
opening a campaign: *is route beta a multi-day FORMAL campaign with an
unlanded brick, or something else?* The answer is neither: the formal
chain is COMPLETE (nothing to land), the open half is a sign CONJECTURE
that all evidence says is false, and the exit's second pillar is the
rung-5 wall itself. RH not claimed.

## 1. Verdict (up front)

GOOD news for register honesty, BAD news for "beta as breakthrough":

* **The beta formal campaign does not exist as a campaign.** The 1080 ->
  1082 -> 1083 -> 1084 -> 1085 chain already landed with audit GREEN
  (1084 §3: "Build completed successfully (3652 jobs). zero `^error:`
  lines; zero `sorryAx`"; all pinned statements on exactly
  `[propext, Classical.choice, Quot.sound]`). There is NO pending Lean
  brick in the beta chain. 1399 §8's phrase "route-β formal prereq"
  needs the correction recorded in section 5 below: the prereq is done;
  what was left open is one inequality.
* **The one open inequality is `0 < arch h.convSq`** for `h` = the
  7-node symmetric root-window interpolant, per off-line zero `rho`
  (`C1HealthyDetectorAnchorReduction` / 1084 §1 item 4-5; unified with
  the record-1080 scalar gate by 1085 §1 item 3: THE SAME Prop).
* **All measurement history says that inequality is FALSE** for the
  current construction: 1077-1079 surrogate `fl2 = -1.294` (quoted in
  1084 §2), 1086 direct measurement NEGATIVE on the frozen real-carrier
  slice, 1087 all 168 Galerkin compressions negative (self-declared
  non-falsifying by its sup-lower-bound law). The exact complex
  computation has never been run — 1403/1404 run it, closing that gap
  with a clean instrument rather than an argument.
* **Even a full success on that inequality would not breach the wall.**
  The root-supported RH exit
  (`sourceRH_of_rootSupportedGate_rightRep_and_endpointCertificates`,
  `C1HealthyDetectorRootSupportExit.lean:110`) consumes TWO hypotheses:
  the gate for every right half-plane zero (the anchor sign) AND the
  universal endpoint-certificate existence, whose content is the
  classical Weil positivity — the same analytic object B0b makes
  equivalent to `SourceRH`
  (`weilCriterion_iff_sourceRH`, `C1WeilCriterionEquivalence.lean:136`).
  Beta re-partitions the wall; it does not lower it.
* **The live mainline already bypasses the beta anchor entirely.**
  `exists_healthyDetectorData_of_sourceNontrivialZero_right`
  (`C1HealthyYoshidaSpectralNegativity.lean:568`) is UNCONDITIONAL
  (hypotheses only about the hypothetical zero itself), and B0b's
  reverse leg consumes exactly that producer
  (`C1WeilCriterionEquivalence.lean:123-126`). The negative side of the
  contradiction engine needs no constructed root-window sign; the wall
  is the positive side. The tower's load-bearing chain is:
  off-line zero -> right representative -> unconditional detector data
  -> `qw g < 0`, versus the gate `0 <= qw g` (all vanishing tests),
  which IS `SourceRH` by B0b. Rung 5 is the only open gate, and it is
  the whole of RH in positivity form.

## 2. The beta register, as it actually stands (source evidence)

+------------------------------------------------------------------------+
| brick | statement | status |
+------------------------------------------------------------------------+
| 1083  | exists_evenOddPair_of_offLineZero: pair (f even, g odd), all |  |
|       | nodal sums, detection value 2, support in +-log2/2, and      |  |
|       | (0 < arch f.convSq + arch g.convSq -> root gate)             | GREEN (1083 rec:|
|       | EvenOddPair.lean:345-421                                     | 0 sorryAx, std   |
|       |                                                             | axioms only)     |
+------------------------------------------------------------------------+
| 1084  | anchor_eq_four_mul_of_even_odd_sum + arch_pair_eq_four_mul: |  |
|       | the pair anchor IS 4 * arch h.convSq; exists_kernelA_final:  | GREEN, 3652 jobs |
|       | one root-window test, triple vanishing, detection, and       | (anchor_reduction1|
|       | 0 < arch h.convSq suffices for the full root gate            | log, 1084 §3)    |
+------------------------------------------------------------------------+
| 1085  | exists_pinnedDetector_of_kernelAInterpolant: the 1084       |  |
|       | inequality and the record-1080 selectedDetectorArchimedean  | GREEN (1085 §1)  |
|       | Gate are the SAME Prop; 0 < arch h.convSq -> detector data  |                  |
+------------------------------------------------------------------------+
| 1081  | rootSupportedHealthyDetectorGate rho (def, :82) + the two-  |  |
|       | pillar RH exit (:110) + damper-free fourth-order tail (:150)| landed           |
+------------------------------------------------------------------------+
| 1375  | exists_healthyDetectorData_of_sourceNontrivialZero_right    | UNCONDITIONAL    |
|       | (SpectralNegativity.lean:568) — fixed windows (1,-1),       | (F3), consumed by|
|       | no support-side hypothesis debt to the anchor sign          | B0b reverse leg  |
+------------------------------------------------------------------------+
| B0b   | weilCriterion_iff_sourceRH (WeilCriterionEquivalence.lean   | machine-checked  |
| (1343)| :136): gate (forall vanishing g, 0 <= qw g) <-> SourceRH    | iff            |
+------------------------------------------------------------------------+

The pillar-B lemma inside the 1081 exit is
`qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf`
(`C1CC20ArchimedeanReadback.lean:133`): certificates produce the sign the
gate asserts. Whatever exact class the certificate hypothesis lives in,
its mathematical content is the positivity half of the explicit formula
— the classical analytic theorem that no construction search can
supply. That is why "finish beta" was never a route through rung 5: the
exit needs BOTH a sign nobody has ever observed positive (pillar A) and
a positivity theorem equivalent to RH (pillar B).

## 3. F14 applied to the beta family (pre-campaign audit promised in 1401 §6)

Law F14 (1401 §4: the (1+eps) taper cannot be an A-shape lever at any
(J1)-feasible geometry) transfers to beta in its STRONGEST form, because
beta has no taper degree of freedom to lose:

* the window is LOCKED by the support obligation at exactly
  +-log 2 / 2 (the sharp Weil window — `Icc (-(Real.log 2 / 2))
  (Real.log 2 / 2)` in both the 1083 theorem and the 1084 final form);
* there is no (Rf, Ru, eps, epsp) grid — the constructed interpolant is
  fixed once rho is fixed; the ONLY scan parameter is the hypothetical
  off-line zero rho itself (rr, im);
* the delta-budget inequality from 1401 applies verbatim to any
  taper-style smoothing of the window (TB grows with the two
  large-|s| nodes rho, -rho, so delta/R stays ~1e-16 or below even at
  the first-zero height; see the 1403 §5 conditioning table for the
  per-cohort numbers before any digit).

So "search the beta grid for a positive anchor" is really
"search a 2-parameter family (rr, im) of one fixed functional".
That is well-posed as ONE probe, not as a campaign, and 1403 runs it.

## 4. Boundary and convention facts the probe inherits (read, not computed)

* `laplaceAt f s = integral of f(x) * exp(+s x)` over the real line —
  the PLUS convention, `CC20YoshidaConvolution.lean:55` (and the
  derivative form `C1XiArithmeticPoleRemainder.lean:34-36` re-quotes it).
  The 1398 instrument's `laplace_g` already integrates `g(x) *
  exp(rho*x)` — same convention, no translation needed.
* The Lean realization `exists_residualWindow_correction`
  (`CC20YoshidaConvolution.lean:295-321`) is NONCANONICAL (finite
  Mellin surjectivity). The model mirror must therefore fix its own
  deterministic representative — exactly the role the solved Gram-
  exponential played for route alpha — and the prereg must say so
  explicitly: the probe measures the NATURAL interpolant class, not a
  Lean-internal choice of correction. A model NEG is evidence about
  this class, and per law 65 it is never a Lean fact about the Lean
  construction (which has uncountably many members; none carries a
  committed sign).
* Node ordering for the mirror: [0, -1/2, +1/2, rho, -rho, -1, +1]
  with target [0, 0, 0, 1, -1, 0, 0] (pairNodeSet/pairNodeTarget,
  `EvenOddPair.lean:185-194`), and rho deliberately placed at index 3
  so the locked instrument's `nodes[3]` frequency proxy (F_at,
  compute_A) applies unchanged.

## 5. Corrections to the register (explicit, dated)

* 1399 §8 and 1401 §4 listed "route-β formal (7-node class) as FORMAL
  PREREQ" among the live levers. After this readback: the formal
  prereq is CLOSED (section 2 table — every bookkeeping brick landed in
  1083-1085 with audit evidence). The live part of that line was only
  (i) the anchor-sign conjecture on the constructed interpolant — model
  evidence against it exists but was never exact-complex — and (ii)
  pillar B of the 1081 exit, which is not a prereq but the wall. No
  committed record claimed otherwise; the phrase simply overstated
  (i)+(ii) as a brick queue. Corrected here; the 6-rung table is not
  changed (rung 3 stays MODEL-NEG on alpha; rung 5 stays the wall).
* Nothing in the freeze-card mainline ("off-line zero => qw(g)<0
  [formal] => 0<=qw(g) [gate] => RH") needs re-deriving: the
  [formal] leg runs through the UNCONDITIONAL producer of section 2,
  not through beta's anchor. The recon confirms the freeze card.

## 6. What 1403/1404 will and will not decide

WILL: produce the first exact-complex model measurement of
`A_beta(rho) := arch h_rho.convSq` — the 1084/1085 object itself — on a
locked (rr, im) cohort, with the 1398 v3 gate battery (GS/GT/GF/GD/GR/
GQ/GV classes) transcribed to n = 7 and a GD extension checking all
seven node values end-to-end (detection AND the three vanishings AND
the two reflected vanishings), plus the F14 re-test (delta scale,
eps-insensitivity) on the 7-node class.

WILL NOT: discharge or falsify anything in Lean (law 65); decide
pillar B (a universal positivity is not a grid question); or make
`rootSupportedHealthyDetectorGate` provable for even one rho if the
sign comes out negative — which the 1077-1087 history predicts. A NEG
outcome retires the beta anchor CONJECTURE (model-level, joining F14's
alpha verdict) and leaves rung 5 as the single open face with the
status of a classical proof obligation. A POS outcome at any cell
would be headline news — it would say pillar A is satisfiable on the
natural class and re-open the 1081 exit as a conjecture — and would
still be MODEL only; TIE and BADCELL are handled by the locked v3
scope rules.

## 7. Next steps

1. 1403 prereg (zero digits, committed before any A_beta value): model
   spec VERBATIM-transcribed from run_1398_rig (gram/lambda_min to n=7;
   SingleOwner replacing the u-f convolution owner since beta's anchor
   is on ONE test; all tolerance classes locked at the v3 values), F12
   conditioning audit table on rung-2 quantities only, cohort
   (rr in {0.55, 0.6, 0.75, 0.9, 0.99}; im in {14.134725, 21.022040,
   25.010858, 100, 1054} with inclusion decided by the audit), tiering
   and sentinel format locked.
2. scripts/run_1403_rig.py + commit prereg and script together, then
   the WSL run under the runner with the standard invN discipline.
3. 1404 outcome record; register closing pass (map README items,
   project memory cards and law notes, all out of tree): the freeze-
   card phrasing "route-beta formal prereq" is superseded by 1402 §5,
   and the new law candidate is that campaign questions are answered
   by reading the exit's HYPOTHESES before costing their
   constructions; commit + push.
