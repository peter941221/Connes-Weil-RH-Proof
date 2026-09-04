# 1121 - T2-rep: the gate-as-quadratic-form matrix representation: pre-registration

Date: 2026-09-04.  Status: PRE-REGISTRATION committed BEFORE any build.
Consumer: T2 (the Stage-B instance for the D1-pinned detector, 1117 s2)
via the 1120 span-discharge corollaries.  The 1118/1119/1120 ABSOLUTE
headline consumes a representation slot `hrep : ICgate w.convolutionSquare
= c (M_true *v c)`; this record LANDS THE GENERATOR of that slot: for a
finite real span of window tests, the gate of the span's convolution
square IS a quadratic form in the coefficients, with matrix read off from
pair gates.  This is the "(iii) matrix-representation lemma" of the 1120
section-5 assessment, sequenced BEFORE the numeric input (iv).

## 0. What lands

Module `ConnesWeilRH/Dev/C1GateMatrixRepresentation.lean`:

  - `spanObj w y`: the packed test of the finite real span
    `sum_i (y i : C) * w i` (compact support by the 1117 finset lemma).
  - `pairTest w i j := (w i).involution.convolution (w j)` - the
    convolution PAIR object; note `pairTest w j j = (w j).convolutionSquare`
    DEFINITIONALLY, so the diagonal of the matrix is exactly the object
    whose gate the 1118/1120 certificates bound by `-mu`.
  - `gateMatrix w : Matrix (Fin k) (Fin k) Real`, entry `ICgate (pairTest)`.
  - `pairFun_support`/`pairFun_integrable`/`pairTest_support_2B`: the
    pair's pointwise convolution integrand is integrable (continuous x
    compact support), and the pair test vanishes outside Ioo (-2B) (2B)
    whenever both factors are supported in Ioo (-B) B (pointwise kill,
    no Mathlib convolution-support API needed).
  - `ICgate_zero_of_test_zero`: gate of the zero test is 0.
  - `ICgate_packTest_sum`: generic accumulator linearity - the gate of
    `G + sum_s F` is `ICgate G + sum_s ICgate F`, by induction with the
    1117 `ICgate_packTest_add` at each insert (common window B carried
    through; partial-sum integrability maintained inductively via
    `archimedeanIntegrand_packTest_add` + `ICintegrable_sum`).
  - HEADLINE `gate_qform_span`: for w supported in a common window B and
    y : Fin k -> Real,
      ICgate ((spanObj w y).convolutionSquare)
        = sum_i sum_j y i * y j * ICgate (pairTest w i j)
        = y (gateMatrix w *v y).
    Proof: convolution integrand expansion at each point (SchwartzMap
    sum/smul applies, star_sum, Complex.real_smul), integral split by
    `MeasureTheory.integral_finsetSum` with per-piece integrability
    (Continuous.integrable_of_hasCompactSupport + HasCompactSupport.mul
    routes), then `ICgate_congr` to the packed double-sum object, the
    packTest linearity chain, and the Finset product/dotProduct algebra.
  - `hrep_of_gateMatrix_eq`: the hrep GENERATOR - if the pair-gate matrix
    equals the committed true matrix M_true, then hrep holds with
    coefficient vector y, exactly the slot consumed by the 1120
    `absolute_spanK`/`absolute_true` headlines.
  - Registered deviation (statement shape only): the per-pair ARCHIMEDEAN
    legality `IntegrableOn (archimedeanIntegrand (pairTest w i j)) (Ioi 0)`
    stays a NAMED HYPOTHESIS of `gate_qform_span` (1117's own pattern:
    "integrability hypotheses are free at use sites" - for squares it is
    discharged by `archimedeanIntegrand_square_integrableOn_Ioi`; the
    pair version needs a pair-owner argument and is booked as a T2-side
    obligation, never silently assumed).

## 1. Gates (registered BEFORE the build)

G1: focused `lake build` of the new module + audit on the ext4 mirror;
    acceptance = "Build completed successfully" footer AND zero `^error:`
    lines.  G2: `#print axioms` on every public declaration, allowed set
    exactly {propext, Classical.choice, Quot.sound}; zero sorry.
G3 (fidelity): an audit example must produce the literal hrep shape
    `ICgate (spanObj phi y).convolutionSquare = y (M_true *v y)` from
    `gateMatrix phi = M_true`.
G4: staged-file hygiene grep 0 matches before every commit.

## 2. Falsifiers (no threshold weakening)

Any step failing to prove => root-caused fix commit; if the POINTWISE
expansion or the pair-support kill fails, the record reports partial and
downgrades the headline to hypothesis form (hpoint named) in the
addendum - never silently.  No existing module may be edited except by a
registered root cause.  RH NOT claimed.

## 3. Run protocol

Commit (prereg + module + audit) BEFORE the first build; one root-caused
fix commit per failing build; post-run addendum after G1-G4.

## 4. Post-run addendum (2026-09-04, after builds 1-3)

VERDICT: LANDED.  Build history, all root-caused per the falsifier
rule: build 1 compiled the prereg-time DRAFT module and failed on
statement-shape errors; the root cause was that the preregistered
accumulator chain does not typecheck - a finite-sum gate identity
needs the sum to carry its compact-support and per-piece integrability
DATA with it - fixed by commit 39cf666, which rebuilt the record
around a packed-finite-sum carrier (shape worked out in a scratch
probe, then backfilled).  Build 2: the MAIN module compiled green
(olean produced; the only error lines in the log are audit-side); the
audit failed on one missing namespace open - `archimedeanIntegrand`
lives in `C1SameOwnerWeil`, which the audit did not open - fixed by
commit e462f85.  Build 3 GREEN: "Build completed successfully
(3636 jobs)", zero `error:` lines, zero `sorry`, exit 0.

G1 PASS (footer + zero error lines).  G2 PASS: 21/21 axiom records
exactly `[propext, Classical.choice, Quot.sound]` (21 `#print axioms`
on every public declaration of the module; wrapped record lines
rejoined before checking), zero `sorryAx`, and zero warnings on the
two new modules - the 153 warnings in the log are BYTE-IDENTICAL
(sorted-line md5 match, diff empty) to 1120's build-1 warning set,
i.e. the pre-existing longLine debt in old modules, nothing new.
G3 PASS: the audit fidelity `example` compiles - from
`gateMatrix w = M_true` it produces the literal hrep shape
`ICgate (spanObj w y).convolutionSquare = y (M_true *v y)` with the
common-window and per-pair-legality hypotheses.  G4 PASS (staged-diff
hygiene greps 0 matches on commits 39cf666 and e462f85).

Deviations from section 0 (statement shape only, all registered here;
no analytic content added or dropped):

  - The generic accumulator `ICgate_packTest_sum` landed as the
    packedSum carrier: `packedSum`/`packedSum_apply`/
    `packedSum_support` plus `archimedeanIntegrand_packedSum`
    (pointwise) and `integrableOn_archimedeanIntegrand_packedSum`
    (partial-sum integrability via `ICintegrable_sum`), and
    `ICgate_packedSum` as the linearity statement, by Finset
    induction with 1117's `ICgate_packTest_add` at each insert -
    exactly the preregistered mechanism, just over a carrier that
    owns its data.
  - Pair lemmas renamed, content unchanged:
    `pairFun_integrable` -> `pairIntegrand_integrable`
    (convolution-existence route via
    `HasCompactSupport.convolutionExists_left_of_continuous_right`),
    `pairFun_support`/`pairTest_support_2B` ->
    `pairTest_apply_of_abs_ge` + `pairTest_support` (pointwise kill,
    no Mathlib convolution-support API, as preregistered).
  - Headline route: the preregistered `ICgate_congr` step was not
    needed - the route lands an OBJECT identity instead:
    `convolutionSquare_spanObj_apply` (pointwise expansion,
    `integral_finsetSum` split, per-pair integrability) gives
    `(spanObj w y).convolutionSquare = packedSum univ (pairPiece w y)`,
    then `ICgate_packedSum`, then `pair_gate_sum_eq_qform`
    (`Fintype.sum_prod_type` + dotProduct algebra).  The preregistered
    pointwise-expansion gate did not fail; it is the first leg of
    `convolutionSquare_spanObj_apply`.
  - `pairTest w j j = (w j).convolutionSquare` landed as `pairTest_self`,
    proof `rfl`, exactly the preregistered definitional diagonal.

The pre-registered deviation is UNCHANGED: the per-pair ARCHIMEDEAN
legality `IntegrableOn (archimedeanIntegrand (pairTest w i j))
(Ioi 0)` is a NAMED HYPOTHESIS of `gate_sum_span`/`gate_qform_span`/
`hrep_of_gateMatrix_eq` (squares discharge it via
`archimedeanIntegrand_square_integrableOn_Ioi`; the pair version needs
a pair-owner argument and stays booked as a T2-side obligation, never
silently assumed).

Consequence for the map: T2-rep step (iii), the matrix-representation
lemma, is LANDED as the hrep GENERATOR: for every finite real span of
window tests with a common window and per-pair legality,
`ICgate ((spanObj w y).convolutionSquare) = y (gateMatrix w *v y)`,
whose entries are the pair gates `ICgate ((w i).involution.convolution
(w j))` - the diagonal entries are exactly the object whose gate the
1118/1120 certificates bound by `-mu`.  With `gateMatrix w = M_true`
this is precisely the representation slot consumed by the 1118/1119/
1120 ABSOLUTE headlines.  Sequencing per the 1120 section-5 assessment:
next is (iv), the real decay input via the 1116c model-consumption
contract.  C2 (drift bound on the TRUE moment table) remains a named
T2-side obligation.  RH NOT claimed.
