# 1117 - the Stage-B bone, formalized: gate-additivity contract + k=1 toy localization

Date: 2026-09-03 (after record 1116 landed). Status: PRE-REGISTRATION
committed BEFORE the first build. The module certifies nothing about the
detector's actual sign; RH NOT claimed; no map change keyed.

## 0. The bone's anatomy, from raw code

1114 §2 states the owed lemma schematically:

    GATE(detector) <= sup { GATE(w) : w in window family covering B }
                    + error(floor, density)        < 0.

The anatomy of GATE decides what formalization is honest. Both summands
are LINEAR functionals of the test function they consume. Raw code
(`ConnesWeilRH/Dev/C1SameOwnerWeil.lean:55-63,161-162`):

    noncomputable def archimedeanNumerator (F : CompactLogTest) (y : Real) : Complex :=
      Complex.ofRealCLM (Real.exp (y / 2)) * (F.test y + F.test (-y)) - 2 * F.test 0
    noncomputable def archimedeanIntegrand (F : CompactLogTest) (y : Real) : Complex :=
      archimedeanNumerator F y / (SelectedWeilSquareOwner.archimedeanDenominator y : Complex)
    noncomputable def archimedeanTerm (F : CompactLogTest) : Real :=
      ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) * F.test 0) +
          ∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y).re
    noncomputable def finitePrimeSum (F : CompactLogTest) : Real :=
      ∑ n ∈ globalPrimeIndexSet F, finitePrimeTerm F n

Why the linearity is load-bearing: the certified side bounds the gate of
EACH window square separately (top <= -pin per class), so a domination
certificate that expresses the detector square as a nonnegative linear
combination of window squares plus a remainder turns the sign problem
into an ADDITIVE bookkeeping of gate values - possible only because the
gate is linear on the space of test functions sharing a support bound
(the prime-sum index sets are support-controlled: a term is nonzero only
at |log n| < B, so a common B makes all three sums compatible).

The integrability question, decided by the same anatomy: the repo proves
`archimedeanIntegrand_square_integrableOn_Ioi` for CONVOLUTION SQUARES
only (owner machinery downstream of `SelectedArchimedeanIntegrability`).
The bridge direction used here NEVER needs a fresh integrability proof:
the defect integrand (F_g's minus the sum of the F_wi's) is pointwise a
finite difference of integrableOn functions (`IntegrableOn.sub`), and its
integral equals the defect gate's integral by pointwise congruence. Zero
new analysis; the whole mechanical layer is algebra + Finset bookkeeping.

The structural datum from 1116 (F1) stays on record: at the TRUE 13-node
delta=0 shape the polynomial-in-chi model detector has GATE/f0 = +0.457,
so a domination contract CANNOT be satisfied by the model configuration -
but law 65 + the floor geometry make that consistent: the model sits on
the critical line (re = 1/2), which `hoff : rho.re <> 1/2` (the detector
hypothesis) and the Platt-Trudgian floor each exclude. Configurations the
contract must serve are exactly the above-floor off-line ones.

## 1. The artifact: `ConnesWeilRH/Dev/C1LocalConfigurationDomination.lean`

Namespace `ConnesWeilRH.Source.C1LocalConfigurationDomination`. Contents:

(1) Gate functional + fidelity re-verification:
    `def ICgate (F : CompactLogTest) : Real := archimedeanTerm F + finitePrimeSum F`
    and `orbitWindowSemiLocalGate g <-> ICgate g.convolutionSquare <= 0`
    by Iff.rfl - the gate of record 1089 is exactly the functional the
    contract consumes (no convention drift, the 1089 file:57-59 anchor).

(2) Linearity layer (fully proved):
    - pointwise `archimedeanNumerator` / `archimedeanIntegrand` additivity
      and real-smul;
    - `finitePrimeSum` rewritten as a sum over a COMMON Finset.range
      ceiling `Nat.ceil (exp B) + 1` for every test supported in
      `Ioo (-B) B` (terms outside vanish: nonzero term forces
      `|log n| < B` through `support_subset_Icc` semantics; index-set
      membership already carries the `term <> 0` condition);
    - the master identity:
      `ICgate g.convolutionSquare =
         ∑ i ∈ s, lam i * ICgate (w i).convolutionSquare +
         ICgate (defect)` where
      `defect = pack (g.sq.test - ∑ i, lam i • (w i).sq.test)`;
      hypotheses: square supports inside a common `Ioo (-B) B` (derived
      from root supports through `convolutionSquare_support_subset_two_mul_Ioo`).

(3) The contraction (the shape the bone must inhabit):
    structure `ICStageBContraction g` with fields
      m, w : Fin m -> CompactLogTest, lam : Fin m -> Real (>= 0),
      B, mu, epsilon;
      square-support hypotheses for g and every w;
      hD     : ICgate (defect) <= epsilon          (the "error(floor, density)"
                                                    slot of 1114 §2);
      hcert i: ICgate (w i).convolutionSquare <= -mu i  (the certified
                                                    window upper bounds -
                                                    consumed as gate-level
                                                    hypotheses: the matrix
                                                    1115 instances + the
                                                    transcendental bridge
                                                    are what supplies them
                                                    class-by-class, the
                                                    same two halves as the
                                                    1112/1115 ledger);
      budget : epsilon <= ∑ i, lam i * mu i.
    and the bridge theorem `orbitWindowSemiLocalGate_of_contraction`:
    contraction data ==> the gate Prop of 1089, which composes (1089
    :63-72 + the D1 headline) into the RH reduction exactly as booked.

(4) Toy localization at k=1 (fully proved):
    `ICStageBContraction_of_below_floor`: given the floor hypothesis
    (every sourceNontrivialZero of height <= H is on the line), a zero
    rho with |rho.im| <= H and hoff : rho.re <> 1/2 yields the
    contraction for every test g by case-split - the vacuous-cell
    discharge. Honest reading: the plumbing accepts a Stage-A-shaped
    hypothesis (a `forall z, Zero z -> height bound -> re = 1/2`
    statement, exactly the Platt-Trudgian form) and outputs the
    domination contract - one cell of the configuration space closed,
    the above-floor cells remaining as instances of the SAME structure.

## 2. What stays OPEN after tonight, named exactly

- (T1, transcendental half): gate-level bounds per window class - the
  1115 instances give matrix-level `isTopBound` on the quotient models;
  the class ==> matrix analysis (the 3 registered axioms) is the
  existing open transfer, unchanged by this record.
- (T2, the bone): above-floor detector configurations, an instance of
  `ICStageBContraction g` for the D1-pinned g of 1089 (window family +
  weights + defect gate bound + budget). 1116 F1 says the finite-window
  convex domination must fail on model spans, hence any T2 instance
  consumes the real iterative correction's decay structure - it cannot
  be manufactured from interpolation data.
No claim that T2 is closeable; no claim RH. This record's deliverable
is that the bone now has ONE type: `ICStageBContraction g`.

## 3. Gates (assertions), registered BEFORE the build

G1 (build): `lake build` of the new module + its audit module on the
   Linux-side mirror; acceptance = log content: "Build completed
   successfully" footer AND zero `^error:` lines.
G2 (no sorry, no axiom drift): the build log must contain no sorry
   warning; the audit module runs `#print axioms` on every new theorem
   - allowed set: {propext, Classical.choice, Quot.sound} (choice is
   already load-bearing for `supportRadius`/`globalIndexBound` upstream
   of any statement here - inherited, not introduced).
G3 (fidelity): the `Iff.rfl` gate re-verification (section 1(1)) must
   close with zero elaboration friction beyond `rfl` - the literal
   1089 gate text and the contract's functional are the same term.
G4 (hygiene): staged-file grep (forbidden local-path / private-artifact
   patterns) before every commit; require 0 matches.

## 4. Artifacts

- docs/proofs/1117_stageB_domination_preregistration.md (this file)
- ConnesWeilRH/Dev/C1LocalConfigurationDomination.lean
- ConnesWeilRH/Dev/C1LocalConfigurationDominationAudit.lean
Run protocol: commit artifacts BEFORE the first build (house law);
every build error gets a root-caused fix batch committed before rerun;
post-run addendum section lands after G1-G4 are evaluated. RH NOT
claimed; no map change keyed.

## 5. Post-run addendum (2026-09-04, after build 8)

Verdict: G1-G4 all PASS. The module and its audit compile clean on the
Linux-side mirror; the Stage-B contract is formalized exactly as
registered. RH NOT claimed; no map change keyed; T1/T2 stand open as §2
named them.

Build trail (house law: every build error root-caused into a committed fix
batch before rerun): pre-run artifacts `1fedac1`; one fix-batch commit per
failed build (`786b549`, `5d6a522`, `17060ac`, `04a647d`, `b7db30a`,
`8469662`, `1b43c9f`, batches 2-7 including the 5b paren re-balance);
error counts across the failed builds declined monotonically
13 -> 5 -> 2 (+ one parse cascade) -> 1 -> 0 in the main module, and build
8 (2026-09-04) is the first green run:

    Build completed successfully (3635 jobs).
    grep -c '^error:' <build-8 log> = 0   (runner exit = 0, first clean exit)

Gate evaluation against §3 (all evidence from the build-8 log):

| gate | verdict | evidence |
|------|---------|----------|
| G1 build green | PASS | footer above; zero `^error:` lines in the whole log; audit module built on top of the already-green main module |
| G2 no sorry, axiom subset | PASS | zero `sorry` matches; all 21 `#print axioms` lists are exactly [propext, Classical.choice, Quot.sound] - choice enters only through the inherited supportRadius/globalIndexBound machinery, as predicted at registration |
| G3 fidelity | PASS | the Iff.rfl proof of orbitWindowSemiLocalGate_iff compiles clean (it would fail elaboration if the two gate texts drifted) |
| G4 hygiene | PASS | every fix batch's staged diff greps 0 forbidden patterns before commit, final commit included |

Non-gate debt recorded for a later cleanup pass: three linter notes in the
main module - `show`-readability at 164:2 and 271:4, unused variable hIf at
423:5. Style-only; G2 as registered gates on sorry/axioms only. (The log
carries 156 warning lines in total; every other one is pre-existing debt in
other modules or lake package-cache noise.)

What build 8 certifies, and what it does not:
- Certifies: the gate functional IS record 1089's gate Prop literally (G3);
  the linearity layer + master identity elaborate with zero sorry;
  `ICStageBContraction g` exists as one inhabitable type whose bridge to the
  1089 gate elaborates at an arbitrary test; the k=1 below-floor cell is a
  real inhabitant (the audit's end-to-end examples compile and typecheck).
- Does not certify: any sign of GATE/f0 for the actual detector. T2 (an
  instance for the D1-pinned g) remains the bone itself; T1 (class ==> matrix
  transfer over the three registered axioms) is unchanged by this record.

Next candidates, each independent of the other and of T2: a cleanup batch
folding the three linter notes, or starting the T1 transcendental-half
transfer.
