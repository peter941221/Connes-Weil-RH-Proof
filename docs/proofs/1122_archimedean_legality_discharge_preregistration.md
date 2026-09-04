# Record 1122 — Discharge of the per-pair archimedean legality (generic archimedean integrability)

Status: PRE-REGISTRATION (committed before any build).
Date: 2026-09-04.
Predecessor: record 1121 (`hrep_of_gateMatrix_eq`, the hrep GENERATOR).
Route: healthy-`CompactLog`, detector-specific semi-local mainline; consumer
= the T2 assembly of the D1-pinned detector (1120 s5 sequencing, item after
(iii)).  RH NOT claimed; no map change keyed.

## 0. Scope and motivation

Record 1121 landed the matrix-representation lemma with ONE named analytic
hypothesis left open on purpose:

    hI : ∀ i j, IntegrableOn (archimedeanIntegrand (pairTest w i j)) (Ioi 0)

(booked as a T2-side obligation; squares discharge their version via
`C1SameOwnerWeil.archimedeanIntegrand_square_integrableOn_Ioi`).

Re-inspection of the square-discharge machinery
(`Source/CCM25Concrete/SelectedArchimedeanIntegrability.lean`) shows its
proof consumes NOTHING square-specific about the test:

  (i)   ContDiff-ness of the archimedean numerator  — for a `CompactLogTest`
        this is `fun_prop` on `exp`, `+`, `*` over the smooth coercion;
  (ii)  numerator 0 = 0 — identity `2*F 0 - 2*F 0 = 0`, TRUE FOR ANY test;
  (iii) eventual vanishing of `F y` and `F (-y)` for large |y| — compact
        support, supplied generically by
        `C1SameOwnerWeil.supportRadius` + `support_subset_Icc`;
  (iv)  the `2 sinh y` denominator facts — test-independent, already proven
        owner-free in the Source layer (derivative, positivity, continuity,
        tail ratio -> 1).

The zero^{+} finiteness is closed by L'Hopital
(`HasDerivAt.lhopital_zero_nhdsGT`, Re and Im separately), exactly as in the
owner file.  Conclusion: the "pair-owner argument" booked by 1121 is not a
new analytic obligation; it is the square argument with the square dressing
removed.  This record lands it ONCE, generically for EVERY `CompactLogTest`,
and deletes the named hypothesis from the hrep generator.

Consequence if it lands: the T2 named-obligation set shrinks to exactly
  (iv) real contraction decay via the 1116c model-consumption contract,
  C2   (drift bound on the TRUE moment table — invoked only on the
        true-table route, not the span route),
  Hnorm (normalization bookkeeping, homogeneous of degree 2).
RH NOT claimed.

## 1. Statement inventory (the contract)

New module `ConnesWeilRH/Dev/C1ArchimedeanIntegrabilityGeneric.lean`,
namespace `ConnesWeilRH.Source.C1ArchimedeanIntegrabilityGeneric`.
Imports `ConnesWeilRH.Dev.C1GateMatrixRepresentation` (for `pairTest`,
`spanObj`, `gateMatrix`, `ICgate`, and the 1121 headlines) and
`ConnesWeilRH.Source.CCM25Concrete.SelectedArchimedeanIntegrability`
(denominator + tail-ratio helpers).

Generic layer (one variable `F : CompactLogTest`):

  G1  archimedeanNumerator_contDiff F : ContDiff ℝ ∞ (archimedeanNumerator F)
  G2  archimedeanNumeratorRe / archimedeanNumeratorIm (defs) and their
      ContDiff lemmas (`reCLM`/`imCLM` composition), plus @[simp] _zero
  G3  archimedeanIntegrand_continuousOn_Ioi F :
        ContinuousOn (archimedeanIntegrand F) (Ioi 0)
  G4  tendsto_archimedeanNumeratorRe_div_denominator_nhdsGT F (and Im twin):
        Tendsto (...) (𝓝[>] 0) (𝓝 (deriv (archimedeanNumeratorRe F) 0 / 2))
      via HasDerivAt.lhopital_zero_nhdsGT
  G5  archimedeanIntegrandLimit F (def) +
      tendsto_archimedeanIntegrand_nhdsGT F
  G6  eventually_archimedeanIntegrand_eq_tail F :
        ∀ᶠ y in atTop, archimedeanIntegrand F y =
          (-2 * F.test 0) * (Real.exp (-y) : ℂ) * archimedeanTailRatio y
      (both F y and F (-y) vanish beyond `C1SameOwnerWeil.supportRadius F`)
  G7  archimedeanIntegrand_isBigO_exp_neg F :
        archimedeanIntegrand F =O[atTop] (fun y => (Real.exp (-y) : ℂ))
  G8  integrableOn_archimedeanIntegrand (F : CompactLogTest) :
        IntegrableOn (archimedeanIntegrand F) (Ioi 0)        ← HEADLINE

Payoff layer (record purpose):

  P1  pairTest_legality {k} (w : Fin k → CompactLogTest) (i j : Fin k) :
        IntegrableOn (archimedeanIntegrand (pairTest w i j)) (Ioi 0)
      := integrableOn_archimedeanIntegrand _
      — the 1121 named hypothesis, DISCHARGED.
  P2  gate_sum_span_free / gate_qform_span_free / hrep_of_gateMatrix_eq_free:
      the 1121 headlines with the `hI` argument REMOVED, proved by feeding
      P1 into the 1121 theorems.  Signatures otherwise identical (window
      hypothesis `hw` retained; `hrep_of_gateMatrix_eq_free` keeps
      `(M_true)` + `hM : gateMatrix w = M_true`).

Audit module `ConnesWeilRH/Dev/C1ArchimedeanIntegrabilityGenericAudit.lean`:
`#print axioms` on every declaration G1-G8, P1, P2, plus G3-gate fidelity
`example`s.

## 2. Mechanism and reuse

Mirror of `SelectedArchimedeanIntegrability.lean` with the owner-specific
inputs replaced:

  owner.convolutionSquare.test        ->  F.test           (any CompactLogTest)
  owner.archimedeanNumerator_contDiff ->  fun_prop chain   (G1)
  owner.supportRadius / _eq_zero_of_abs_gt
                                      ->  C1SameOwnerWeil.supportRadius F
                                          + support_subset_Icc
  owner-free helpers REUSED as-is (imported, not re-proven):
    hasDerivAt_archimedeanDenominator,
    archimedeanDenominator_deriv_ne_zero, archimedeanDenominator_pos,
    archimedeanDenominator_contDiff, archimedeanDenominator_zero,
    archimedeanTailRatio, tendsto_archimedeanTailRatio_atTop,
    HasDerivAt.lhopital_zero_nhdsGT route,
    exp_neg integrability + IntegrableAtFilter packaging.

Zero numeric content: no probe, no data, no thresholds.  The record is pure
Lean analysis over existing objects.

## 3. Risks / pre-registered deviation policy

  R1  `fun_prop` may refuse the exact `archimedeanNumerator` composition;
      fallback = explicit ContDiff derivation chain (exp/CLM/mul/add).  This
      is a PROOF-side deviation only; statement shapes above are the contract.
  R2  L'Hopital API shapes are pinned by the owner file (same Mathlib v4.30),
      so no deviation is expected on G4.
  R3  If any step of G8 genuinely cannot close, the record registers the
      root cause and a fix batch; the scope does NOT shrink below G8+P1+P2.

## 4. Gates and protocol

  G1  (build) focused `lake build ConnesWeilRH.Dev.C1ArchimedeanIntegrability
      Generic ConnesWeilRH.Dev.C1ArchimedeanIntegrabilityGenericAudit` on the
      ext4 build mirror via the resource runner: footer
      "Build completed successfully (N jobs)" AND zero `^error:` lines AND
      zero `sorry`.  Acceptance = log content, not exit code.
  G2  (axioms) every `#print axioms` in the audit prints exactly
      `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, nothing else.
  G3  (fidelity) audit `example`s: (a) P1 instantiated on an abstract pair
      `pairTest w i j`; (b) `hrep_of_gateMatrix_eq_free` returns the literal
      T2 slot `ICgate ((spanObj w y).convolutionSquare) = y ⬝ᵥ (M_true *ᵥ y)`
      with NO `hI` hypothesis in sight.
  G4  (hygiene) staged-diff grep on EVERY commit of this record: no
      `sorry`/`admit`/`sorryAx`, no private artifacts, no local paths.

Protocol: this preregistration commits BEFORE the first build; one
root-caused fix commit per failing build; zero threshold changes (no
thresholds exist); post-run addendum appended to this file after the gates.

## 5. Map consequence (post-landing, to be confirmed by the addendum)

The 1121 hrep generator loses its only analytic named hypothesis; the ABSOLUTE
headline slot of 1118/1119/1120 is then reachable for a window span with ZERO
named legality hypotheses, leaving the T2 assembly exactly:
  (iv) real contraction decay (1116c contract) — the one true numeric input,
  C2 + Hnorm as booked above.
No route selection changes; no map record edit beyond the routine frontier
note; RH NOT claimed.

## 6. Post-run addendum (2026-09-04, after builds 1-2)

VERDICT: LANDED.  Chain: prereg `77372d6` committed BEFORE any build ->
module draft `01127b7` -> build 1 FAILED (6 error sites) -> one fix batch ->
build 2 FULL GREEN.

Build 1 root causes (three mechanisms, one fix batch):
  (a) missing scoped opens - `𝓝` / `𝓝[>]` need `open scoped Filter` (the
      six "unexpected token '>'" / "Unknown identifier 𝓝" sites are ONE
      root cause), and `⬝ᵥ` / `*ᵥ` need `open Matrix` (subscriptTerm
      elaborator, the gotcha already banked from record 1118);
  (b) numerator-zero lemmas - `simp [def]` alone does not close the `.re`
      form; mirrors the owner route: prove `archimedeanNumerator F 0 = 0`
      by `simp [archimedeanNumerator]; ring` first, then `.re` / `.im`
      zero by simp through it;
  (c) the support contradiction `supportRadius F < y` vs `y <= supportRadius
      F` closed by linarith - `LT.lt.not_le` dot-projection resolved into
      the nonexistent `Real.lt.not_le` in this Mathlib build.

Build 2: FULL GREEN - "Build completed successfully (3637 jobs)", zero
`^error:` lines, zero `sorry` (main module 45 s, audit 1.2 s).
G1 PASS.  G2 PASS: 19/19 `#print axioms` records exactly
`[propext, Classical.choice, Quot.sound]` (lines rejoined across wraps,
zero non-standard, 19 unique declarations).  G3 PASS: both fidelity
`example`s compile - the pair legality at an abstract pair, and the free
hrep headline returning the literal T2 slot with NO legality hypothesis.
G4 PASS after one hygiene fix: the prereg had leaked the local mirror
path; genericized to "the ext4 build mirror" (house style; zero committed
repo documents contain the path).  Warnings: the log's 153 warnings are
the pre-existing old-module set (same count as the 1119/1120/1121
builds); ZERO warnings on the two new modules.

Deviations: NONE on the preregistered statement shapes.  One ADDITIONAL
declaration beyond the prereg list: `archimedeanNumerator_zero` (the
intermediate lemma required by root cause (b)) - additive, audited.

Consequence: the 1121 named hypothesis
`∀ i j, IntegrableOn (archimedeanIntegrand (pairTest w i j)) (Ioi 0)` is
DISCHARGED.  `pairTest_legality` proves it for every pair of window tests
with no data input; `gate_sum_span_free` / `gate_qform_span_free` /
`hrep_of_gateMatrix_eq_free` restate the 1121 headlines with the `hI`
argument removed.  The generic headline subsumes the square case too; the
existing `archimedeanIntegrand_square_integrableOn_Ioi` route is left
untouched for its current consumers (backward compatible, 1121 statements
unchanged).  T2 named-obligation set after this record: exactly
  (iv)  real contraction decay via the 1116c model-consumption contract,
  C2    drift bound on the TRUE moment table (true-table route only),
  Hnorm normalization bookkeeping.
RH NOT claimed; no map change keyed.
