# 1095 - P2/S2 per-term nuclearity closure: name S2's actual summands, glue via isTraceClassAlong_sub

Date: 2026-09-02. Follows record 1094 (`C1ProlateRootCommutatorBalancedLegContractReduction`,
GREEN + warning-clean), which named the owed analytic contract as per-term nuclearity of the two RAW
commutator terms `C ∘ K_S` and `K_S ∘ C`. This record refines that naming to **S2's actual summands**
and proves the closure in one line. RH unclaimed; GATE 1 mainline untouched; non-mainline / gated
(local build green, not yet committed).

Numbering: takes the next free number **1095**, out of sequence alongside this producer thread's
1090/1091/1092/1093/1094 (all committed as `ab3f66f`). Committed mainline HEAD is record 1087;
1088/1089 are reserved in prose for mainline and neither is double-claimed here.

## 0. Verdict up front

```text
ROUTE = S2's remainder has a LEADING C†, so its two summands are the WITH-C† terms, not record 1094's raw ones:

  targetProlateDetectorRootCommutatorRemainder owner family
      = C† ∘ cc20Commutator(C, K_S)
      = C† ∘ (C ∘ K_S - K_S ∘ C)
      = [C† ∘ (C ∘ K_S)]  -  [C† ∘ (K_S ∘ C)]          (comp distributes over sub; comp_add/_sub)

PROVEN here (committed machinery only):
  def   ...LeftSummand / ...RightSummand        the two named WITH-C† summands.
  thm   ...Remainder_eq_twoSummandDiff           the S2 remainder IS their signed difference (ext x; simp).
  def   ...SandwichedTermNuclearity             THE OWED CONTRACT: each WITH-C† summand is IsTraceClassAlong.
  thm   ..._of_perTermNuclearity                S2 follows from that nuclearity ALONE, one line via isTraceClassAlong_sub.

Genuinely OWED analytic contract (NAMED, not yet discharged in Lean):
  targetProlateDetectorRootCommutatorSandwichedTermNuclearity : each WITH-C† summand has a summable DIAGONAL.
      PROBE-P2's flat O(1) (~4.63, decreasing) transfers to it up to the fixed constant ‖C‖ (window-independent).

SUPERSEDES record 1094's no-C† naming as the canonical owed contract for S2: this route needs NO bare-root
contract (#1/#2), so it sidesteps the false-for-continuum-carrier root-HS premises entirely.
```

## 1. Why name the WITH-C† summands, not record 1094's raw terms

Record 1094 named per-term nuclearity on `C ∘ K_S` and `K_S ∘ C`. But the leaf's S2 target is not their
difference — it has a **leading adjoint** (leaf :229): `targetProlateDetectorRootCommutatorRemainder =
C† ∘ cc20Commutator(C, K_S)`, and `cc20Commutator A W := A.comp W - W.comp A` (CCM24/ThreeBranchCommutatorLedger).
So S2's true summands are:

```text
  LEFT  = C† ∘ (C ∘ K_S)          RIGHT = C† ∘ (K_S ∘ C)
```

Going from record 1094's raw-term nuclearity to these would require "bounded left multiplication by `C†`
preserves IsTraceClassAlong". That lemma is NOT committed, and it is in fact **false** for the bare
conditional-diagonal definition of `IsTraceClassAlong basis T := Summable fun i => ⟪basis i, T(basis i)⟫`:
a bounded map can take a diagonally-summable operator to one whose diagonal need not be summable (the
diagonal entries are products that do not inherit conditional summability from the factor). Naming the
WITH-C† summands directly avoids needing that lemma at all — and it is exactly what PROBE-P2 measured, so no
analytic strength is lost:

+-------------------------------------------------+------------------------------------------+
| quantity                                        | status                                   |
+-------------------------------------------------+------------------------------------------+
| raw term C ∘ K_S nuclear (record 1094's name)   | flat O(1), ~4.63, decreasing             |
| WITH-C† summand C† ∘ (C ∘ K_S) nuclear          | ≤ ‖C‖ × that; ‖C‖ window-independent     |
+-------------------------------------------------+------------------------------------------+

`‖C‖ = ‖F h‖_inf` is a fixed constant independent of the frequency window, so multiplying by it preserves
the "flat O(1), decreasing" nature PROBE-P2 certified. The named contract below is therefore the SAME analytic
fact as record 1094's, stated on the operators S2 actually contains — strictly more convenient for the glue.

## 2. What is PROVEN here vs OWED

PROVEN in `Dev/C1ProlateRootCommutatorPerTermNuclearityGlue.lean` (module builds GREEN; the only log line
naming it is its build marker `✔ [3199/3199] Built …PerTermNuclearityGlue (33s)`, zero warning/error lines
name the file; WSL ext4 replay, `Build completed successfully (3199 jobs)`):

```text
  def   targetProlateDetectorRootCommutatorLeftSummand      C† ∘ (C ∘ K_S)
  def   targetProlateDetectorRootCommutatorRightSummand     C† ∘ (K_S ∘ C)
  thm   ...Remainder_eq_twoSummandDiff                      remainder = LEFT - RIGHT   (ext x; simp [.., cc20Commutator])
  def   targetProlateDetectorRootCommutatorSandwichedTermNuclearity      THE OWED CONTRACT (both summands IsTraceClassAlong)
  thm   ..._of_perTermNuclearity                             S2 from that nuclearity ALONE, one line via isTraceClassAlong_sub
```

The glue theorem's body is:

```lean
have hsub : IsTraceClassAlong globalBasis (LEFT - RIGHT) :=
    isTraceClassAlong_sub globalBasis LEFT RIGHT hnuc.1 hnuc.2
simpa [targetProlateDetectorRootCommutatorTraceLegality, ...Remainder_eq_twoSummandDiff] using hsub
```

i.e. `isTraceClassAlong_sub` (the committed two-sided closure of the conditional-diagonal property) plus the
operator-identity theorem that S2's remainder equals `LEFT - RIGHT`. The leaf def is added to the simp set so
it unfolds; `…_eq_twoSummandDiff` then rewrites the argument position of `IsTraceClassAlong`.

OWED to producers (none is a Lean proof yet):

```text
  1. Discharge targetProlateDetectorRootCommutatorSandwichedTermNuclearity in Lean: formalize PROBE-P2's flat
     O(1) per-summand nuclear-norm bound (~4.63, decreasing). This is the analytic core and needs its own record.
  2. Owner transfer: Gaussian stand-in root -> actual selected convolution root per-owner (bounded bookkeeping;
     record 1090 Q1 shows any Schwartz h qualifies identically).
```

## 3. Relationship to record 1094's naming (supersession note)

Record 1094 named `targetProlateCommutatorTermNuclearity` on the RAW terms `C ∘ K_S` / `K_S ∘ C`. This record
names a DIFFERENT, S2-correct contract:

```text
+----------------------------------------------------------+--------------------------------------------------+
| name                                                     | operators                                        |
+----------------------------------------------------------+--------------------------------------------------+
| 1094 targetProlateCommutatorTermNuclearity               | C ∘ K_S  and  K_S ∘ C        (raw, NO leading C†) |
| 1095 ...SandwichedTermNuclearity   (THIS, canonical)     | C† ∘ (C ∘ K_S)  and  C† ∘ (K_S ∘ C)              |
+----------------------------------------------------------+--------------------------------------------------+
```

They are the same analytic fact up to the fixed bounded factor ‖C‖ (section 1). The 1095 version is the one
that closes S2 in a single `isTraceClassAlong_sub` with NO bare-root contract, so it is promoted as canonical;
1094's def stays committed and standalone (nothing consumes it yet), superseded for the closure only.

## 4. Honesty ledger

- Adds ONE Lean module + this doc; no change to the leaf S2 statement, the two-contract F1′ corollary, or GATE 1 mainline.
- RH unclaimed. Non-mainline / gated (local build green + warning-clean for this file; not committed).
- The glue is PROVEN from committed machinery only (`isTraceClassAlong_sub` + an `ext x; simp` operator identity).
  The nuclearity contract it assumes is NAMED but NOT yet DISCHARGED in Lean — that analytic discharge plus owner
  transfer are the producer's remaining targets (section 2, owed items 1–2).

## 5. Next steps

1. [DONE this record] Land `Dev/C1ProlateRootCommutatorPerTermNuclearityGlue.lean` green + warning-clean: name
   S2's actual WITH-C† summands, prove the operator identity, and close S2 from per-term nuclearity in one line via
   `isTraceClassAlong_sub`.
2. OWED - discharge `...SandwichedTermNuclearity` in Lean (formalize PROBE-P2's flat O(1) ~4.63 on the WITH-C†
   summands); this is the analytic core and its own record.
3. OWED - owner transfer stand-in Gaussian root -> actual selected convolution root per-owner, then commit 1095 with
   the hygiene gate (non-mainline payload): promote the one-line `isTraceClassAlong_sub` closure as canonical for S2.
