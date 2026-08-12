# 991 -- M2WidthPlateau carriers: sign, Lean eval-feasibility, counterexample verdict

Date: 2026-08-11. Status: numeric evidence + source audit. RH NOT claimed.
Lean carrier: ConnesWeilRH/Dev/M2WidthPlateau.lean (narrowC wideC narrowPsi widePsi,
healthyQw_decomposition). Companion: docs/proofs/991_m2_widthplateau_carrier_sign.py.

## 1. The two carriers

narrowC = width 6/5, support [-6/5,6/5], M2 window 12/5 = 2.4 (< 2.82, the 990 positive side)
wideC   = width 3/2, support [-3/2,3/2], M2 window 3         (> 2.82, the 990 negative side)

healthyQw narrowC / wideC read the healthy psi (pole - arch - finite-prime-{2}) at
these carriers as Lean expressions (no sign/bound asserted).

## 2. Task 1: sign of narrowC vs wideC (resolution-stable numeric)

Rows: carrier | N | arch | pole | term2 | psi | A.

  narrowC [-1.2,1.2]  10001  arch -0.01513  pole -0.00185  term2 -0.01299  psi +0.026260  A 0.06320
  narrowC [-1.2,1.2]  20001  arch -0.01515  pole -0.00181  term2 -0.01300  psi +0.026337  A 0.06326
  narrowC [-1.2,1.2]  40001  arch -0.01517  pole -0.00179  term2 -0.01299  psi +0.026374  A 0.06323
  wideC   [-1.5,1.5]  10001  arch +0.00145  pole -0.00491  term2 +0.00697  psi -0.013328  A 0.10040
  wideC   [-1.5,1.5]  20001  arch +0.00144  pole -0.00484  term2 +0.00698  psi -0.013261  A 0.10047
  wideC   [-1.5,1.5]  40001  arch +0.00141  pole -0.00481  term2 +0.00697  psi -0.013188  A 0.10043

Three-Mellin vanish M0/Mh/M1 ~ 1e-15 in every case (in-domain finite-vanishing test).
A = ||g||^2 holds within the 989 assert.

Result:
- narrowC psi is positive (+0.0263), stable across N.
- wideC psi is negative (-0.0132), stable, matches 989 [-1.5,1.5] -0.0132.
So the sign flip (positive narrow / negative wide) reproduces exactly on the two Lean
carriers.

## 3. Task-2: can Lean evaluate the psi sign?

No, not with the current definitions. Every healthy-psi constituent is a noncomputable
analytic integral: poleFunctional (Mellin), totalArchimedean = compactArchimedeanTerm
(Lebesgue), sourceFinitePrimeTerm (vonMangoldt times an integral of values). norm_num /
#eval cannot grind such integrals into a decimal. A Lean-side certified quadrature
(interval_integral-based bound with error control, or an explicit algebraic test whose
integrals are computable) would be a NEW separate deliverable; none exists in this repo
today. This is why the project uses numpy numerics for the psi numbers.
(flagged as an open leaf, not fabricated).

## 4. Task-3: is the narrow psi > 0 a candidate counterexample?

No, as of today. The reason is the gap between the numeric full-psi and the wired
criterion slot.

The C1 criterion gate is weilLocal <= 0 on starG = conv^2 g. On the healthy carrier the
wired healthyCC20TestSpace.weilLocalSum reads ONLY the archimedean slot:

    weilLocalSum g = - totalArchimedean (convolutionSquare g).test      (= - arch)

while the numeric healthy-psi is the FULL form (pole - arch - prime):

    psi = poleFunctional - totalArchimedean - sourceFinitePrimeTerm(2)   (= pole - arch - prime)

So the narrow psi>0 is not immediately a contradiction of the wired sign,
because the wired slot omits the pole and prime terms. Turning narrow psi>0 into a
formal counterexample requires TWO genuinely-open bridges, both absent:

1. an identity (hardcoded) equating the criterion's weilLocalSum on conv-g with the full
   healthyPsi (the pole+prime must enter). Without it, a positive psi is not the
   criterion's sign.  (This is the same operator/scalar seam the route calls open, docs/proofs/963 #1.)
2. the Lean carrier narrowC must carry the ortho-{0,1/2,1}-vanish residual that the
   numerics use; M2WidthPlateau does NOT build it (that construction stays open).

Therefore narrowC's psi>0 is a reproducible, resolution-stable, in-domain FALSIFICATION
DIRECTION signal, but it is NOT a formal counterexample and does not refute the
criterion today.

## 5. Bottom line

- (1) concrete resolution-stable sign table for the exact Lean carriers delivered.
- (2) Lean-internal sign evaluation is blocked by the absence of integral-eval
  machinery (open deliverable, not fabricated).
- (3) narrow psi>0 is a direction signal, pending the full-psi==weilLocal bridge + the
  ortho-vanish residual on the carrier, so "candidate counterexample" is not firm.

RH NOT claimed at any step.


## 6. Addendum (2026-08-11): the algebraic seam is now a Lean theorem

The open bridge #1 of section 4 is now proven axiom-clean in
ConnesWeilRH/Dev/M2WidthPlateau.lean as

    theorem healthyQw_eq_weil (c : CompactLogTest) :
      healthyQw c = healthyCC20TestSpace.weilLocalSum c
                   + poleFunctional (conv² c).test
                   - sourceFinitePrimeTerm 2 (conv² c).test

(unfold healthyQw/healthyPsi, rw [C1.healthyWeilReadoff c], ring).  WSL green,
axioms [propext, Classical.choice, Quot.sound], 0 sorry.  It restates exactly
section-4's relation psi = weilLocalSum + (pole - prime): the wired
weilLocalSum holds only -arch, and the pole+prime corrections are the full
healthyPsi.

What this does NOT do:
- It does not compute either side (the terms remain noncomputable integrals).
- It does not assert a sign on the wide/narrow carriers (no healthyQw <= 0).
- It does not build the ortho-{0,1/2,1}-vanish residual on narrowC, which is
  still the second, genuinely-open bridge (section 4 item 2) needed to turn
  narrow psi>0 into a formal counterexample.

Hence the bottom-line judgement in section 5 is unchanged: the algebraic seam
is closed, but the counterexample / sign decision still forks on the (pole-prime)
residual and the missing ortho-vanish carrier construction. RH NOT claimed.
