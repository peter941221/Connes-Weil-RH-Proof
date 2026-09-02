# 1096 - P2/S2 sandwiched nuclearity discharge: S2's owed contract drops to a single A-in-HS obligation

Date: 2026-09-02. Follows record 1095 (`C1ProlateRootCommutatorPerTermNuclearityGlue`,
COMMITTED + PUSHED as `c16c94f`), which named the canonical owed contract for S2 as per-term
nuclearity of the two WITH-C-dagger summands and proved that S2 follows from it in one line via
`isTraceClassAlong_sub`. This record **DISCHARGES** that named contract down to a single primitive
analytic obligation about the prolate factor A (whose positive square is K_S). RH unclaimed; GATE 1
mainline untouched; non-mainline / gated (local build green, not yet committed).

Numbering: takes the next free number **1096**, out of sequence alongside this producer thread's
1090/1091/1092/1093/1094 (committed as `ab3f66f`) and 1095 (`c16c94f`). Committed mainline HEAD is
record 1087; 1088/1089 are reserved in prose for mainline and neither is double-claimed here.

## 0. Verdict up front

```text
ROUTE = record 1095's owed contract (both WITH-C† summands IsTraceClassAlong) DISCHARGES to ONE primitive:

  targetProlateRemainderFactorHS : Summable fun i => ‖A e_i‖^2      (A in HS, A = prolate factor, K_S = A† . A)

Why it works: each WITH-C† summand is a BOUNDED SANDWICH of K_S written as an HS-legs trace product.
  LEFT   = C† ∘ (C ∘ K_S)      = P ∘L K_S-as-traceProduct,            with P := C† ∘ C and right-bounded = id
  RIGHT  = C† ∘ (K_S ∘ C)     = C† ∘L K_S-as-traceProduct ∘L C,        bounded on both sides

The committed `boundedSandwich_isTraceClassAlong` closes each sandwich from A in HS ALONE. The root C
enters only as a BOUNDED dressing (never assumed Hilbert--Schmidt) - exactly the continuum-correct
posture records 1094 and 1095 drove at: on L2(R, volume) a generic Schwartz-symbol convolution root is
NOT compact, so any "C in HS" premise would be false; here C is only ever `bounded`.

PROVEN here (committed machinery only):
  def   targetProlateRemainderFactorHS                 A in HS along globalBasis (THE primitive owed contract).
  def   targetProlateRemainderHSPairData               K_S as a BasisHilbertSchmidtPairData with both legs = A.
  thm   ...traceProduct_eq                             that pair data's trace product IS K_S (leaf adjoint_comp_self).
  thm   ...LeftSummand_isTraceClassAlong               LEFT is trace-legal from A in HS alone (boundedSandwich, P + id).
  thm   ...RightSummand_isTraceClassAlong              RIGHT is trace-legal from A in HS alone (boundedSandwich, C† + C).
  thm   ...SandwichedTermNuclearity_of_FactorHS        the record-1095 owed contract follows: constructor on both summands.

Genuinely OWED analytic core now STRICTLY NARROWER than before: prove A in HS on the continuum carrier
(= Tr K_S < inf, finite per family; record 1067 measured Tr K_S growing but finite, 16 -> 34 over four octaves).
```

## 1. Why a bounded sandwich discharges nuclearity from A-in-HS alone

`boundedSandwich_isTraceClassAlong` (`Source/CC20Concrete/HilbertSchmidtIdeal.lean:599`) says: given an
HS-legs pair data `PD`, and ANY two bounded maps `L`, `R`, the operator `L ∘ PD.traceProduct ∘ R` is
`IsTraceClassAlong` on **the pair data's own source basis**. It re-expresses the sandwich as a fresh
pair-data trace product (left leg = `PD.left ‹then› L`, right leg = `R ‹before› PD.right`), so it works
from A in HS alone with no further hypothesis. That is precisely why C never has to be assumed HS:

```text
+---------------------------------------------------+-----------------------------------------------+
| summand                                           | bounded sandwich of K_S-as-traceProduct                |
+---------------------------------------------------+-----------------------------------------------+
| LEFT  = C† ∘ (C ∘ K_S)                            | left-bounded P := C† ∘ C,   right-bounded = id             |
+---------------------------------------------------+-----------------------------------------------+
| RIGHT = C† ∘ (K_S ∘ C)                            | left-bounded C†,         right-bounded = C                 |
+---------------------------------------------------+-----------------------------------------------+
```

The LEFT summand is `P ∘ K_S` with the right dressing trivially the identity; the RIGHT summand is a
genuine two-sided sandwich by `C†` and `C`. In both cases the middle factor is exactly K_S, written as
the trace product of the A/A pair data (record 1095's leaf fact
`targetProlateRemainderFactor_adjoint_comp_self`: A† ∘ A = K_S). Boundedness of C and hence P and C† is
plain: C is a Fourier multiplier, `‖C‖ = ‖F h‖_inf < inf`.

## 2. What is PROVEN here vs OWED

PROVEN in `Dev/C1ProlateRootCommutatorSandwichedNuclearityDischarge.lean` (module builds GREEN +
warning-clean, the only log line naming it is its build marker; WSL ext4 replay,
`Build completed successfully (3200 jobs)`):

```text
  def   targetProlateRemainderFactorHS                       Summable ‖A e_i‖^2  - THE primitive owed contract.
  def   targetProlateRemainderHSPairData                     BasisHilbertSchmidtPairData with both legs = A (from hA).
  thm   ...traceProduct_eq                                   pairData.traceProduct = K_S (leaf adjoint_comp_self, one line).
  thm   ...LeftSummand_isTraceClassAlong                     LEFT trace-legal from A in HS alone.
  thm   ...RightSummand_isTraceClassAlong                    RIGHT trace-legal from A in HS alone.
  thm   ...SandwichedTermNuclearity_of_FactorHS              the record-1095 owed contract follows (constructor).
```

The two summand lemmas are one-line each after naming a local `PD`; the LEFT lemma additionally drops an
identity factor (`P ∘ K_S = P ∘ K_S ∘ id`), which the leaf's identity-drop idiom handles by adding
`ContinuousLinearMap.id ℂ finiteSCarrier` and `ContinuousLinearMap.comp_id` to the simp set together with
the local lets (a local let name must be in the simp set for it to unfold, so its traceProduct identity
fires).

OWED to producers (none is a Lean proof yet):

```text
  1. Prove targetProlateRemainderFactorHS on the continuum carrier: A in HS (= Tr K_S < inf), finite per family.
     Record 1067 measured Tr K_S growing but FINITE over four octaves (16 -> 34) - a boundedness/decay
     statement about the prolate factor, not a bare-root contract. Its own record.
  2. Owner transfer: Gaussian stand-in root -> actual selected convolution root per-owner (bounded
     bookkeeping; record 1090 Q1 shows any Schwartz h qualifies identically). Once A in HS is proved PER
     owner-family with the selected root, both summand lemmas apply unchanged since C enters only as bounded.
```

## 3. Contract-narrowing chain (supersession table)

Each S2 brick in this thread weakens the owed analytic premise; 1096 lands at the narrowest form yet -
a single A-in-HS contract with NO bare-root (C-in-HS) assumption:

```text
+----------+-------------------------------------------------+-----------------------------------------------+
| record   | owed contract                                     | root C's role                                   |
+----------+-------------------------------------------------+-----------------------------------------------+
| 1065     | F_K in HS (= Tr K_S < inf), base (F_K,F_K)       | needed F_K itself HS; FAILS for {2,3,5}         |
+----------+-------------------------------------------------+-----------------------------------------------+
| 1093     | three named contracts #1(C in HS)/#2/#3(K_S in HS)| C enters as a bare-root HS leg (false on cont.) |
+----------+-------------------------------------------------+-----------------------------------------------+
| 1094     | per-term nuclearity of C o K_S / K_S o C         | C only bounded at the col-sum level             |
+----------+-------------------------------------------------+-----------------------------------------------+
| 1095     | per-term nuclearity of the WITH-C† summands      | glue via isTraceClassAlong_sub, no bare-root    |
+----------+-------------------------------------------------+-----------------------------------------------+
| 1096     | A in HS ALONE (= Tr K_S < inf)                   | C only ever BOUNDED dressing (THIS record)      |
+----------+-------------------------------------------------+-----------------------------------------------+
```

1096 keeps the WITH-C† summand names of record 1095 (the canonical S2-correct contract) and proves it
from A-in-HS alone; records 1093/1094's bare-root premises are no longer on the critical path. The
narrowing is strict: "A in HS" implies none of the false-for-continuum-carrier "C in HS" contracts, and
is strictly weaker than record 1065's F_K-in-HS base (which failed for {2,3,5}).

## 4. Honesty ledger

- Adds ONE Lean module + this doc; no change to the leaf S2 statement, the two-contract F1' corollary, or GATE 1 mainline.
- RH unclaimed. Non-mainline / gated (local build green + warning-clean for this file; not committed).
- The discharge is PROVEN from committed machinery only (`boundedSandwich_isTraceClassAlong` + the leaf's
  `targetProlateRemainderFactor_adjoint_comp_self`). The primitive contract it assumes, A in HS, is NAMED but NOT
  yet PROVEN on the continuum carrier - that analytic statement plus owner transfer are the remaining producer targets.

## 5. Next steps

1. [DONE this record] Land `Dev/C1ProlateRootCommutatorSandwichedNuclearityDischarge.lean` green + warning-clean:
   discharge record 1095's sandwiched nuclearity contract to a single A-in-HS obligation via the committed
   `boundedSandwich_isTraceClassAlong`, with C entering only as bounded dressing on both WITH-C† summands.
2. OWED - prove `targetProlateRemainderFactorHS` (A in HS = Tr K_S < inf) on the continuum carrier, finite per
   family; record 1067's 16 -> 34 finite-growth measurement is the model witness that it is a boundedness/decay
   statement about the prolate factor, not a bare-root contract. Its own record.
3. OWED - owner transfer stand-in Gaussian root -> actual selected convolution root per-owner (bounded bookkeeping),
   then commit 1096 with the hygiene gate (non-mainline payload): promote "S2's owed contract = A in HS alone" as
   canonical, retiring the bare-root premise of records 1093/1094 from the critical path.

## 6. Erratum (records 1097/1097b/1098, 2026-09-02)

The pre-registered primitive fork fired H1-REJECTED / H2-CONFIRMED at the
certified deep octave: the raw trace `Tr K_S` - which is what
`targetProlateRemainderFactorHS` requires - KEEPS its power law at
`xi_max = 204.8` (34.2696 -> 41.0499, slope16x +0.335, no bend, all
certification gates green), while the law-16 weighted legs stay O(1).
This record's discharge is therefore DEMOTED to a valid-but-unschedulable
implication: the Lean content is correct (build green, clean axioms, the
implication `A in HS => SandwichedTermNuclearity` stands), but its
primitive is the record-1063-falsified raw-F1 class, so no producer work
may schedule it.  The canonical S2 primitive set is (a)
`targetProlateDetectorAbsorbedFactorHS` + (b)
`targetProlateDetectorRootCommutatorTraceLegality`, wired by record 1098
(`C1ProlateRootCommutatorAbsorbedLegalityDischarge.lean`); section 5 item
2 above is SUPERSEDED by that re-point, and section 3's narrowing chain
now ends at "1096 A-in-HS (demoted) - 1098 (a)+(b) canonical".  Evidence:
`docs/proofs/1097_p2_contract_fork_preregistration.md` (ABORT as
registered), `1097b_p2_deep_octave_bracket_preregistration.md` (verdict),
`1098_p2_s2_absorbed_legality_discharge.md` (re-point brick).  NUMERICAL
evidence level; RH unclaimed.
