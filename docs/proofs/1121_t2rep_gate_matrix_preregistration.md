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
