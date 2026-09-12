# Record 1365 (DESIGN + LOCKED STATEMENTS) - TARGET-A2 counting frame: the enemy gets a Lean name; definitions-side L2c (pre-build lock, law 42)

```text
+---------------------------------------------------------------------+
| What it is: the definitions-side brick 1362 s6 item 4 adjudicated    |
| after L1 landed: counts (Set.encard), f*(A) = A/(A+2) algebra, and  |
| the A2 statement as a NAMED Lean schema - with A left UNINTERPRETED |
| on record, because its realization IS L2c.                          |
| Why: the direct-attack order needs the enemy inside the register.    |
| This brick proves zero analysis; it machine-verifies the RH-side     |
| collapse (off-count = 0) and states exactly what the remaining       |
| margin is (A > 0). RH NOT claimed.                                  |
| Lock discipline: all statements below committed BEFORE any build     |
| log; batch number assigned at launch (next free).                   |
+---------------------------------------------------------------------+
```

## 1. Adjudication of "L2c-formal, definitions-side" (1362 s6.4)

Can A(I)/N(I) be realized from the committed dictionary without new
analysis? Verdict, per object:

  N(I): YES - Set.encard on the 1363 windowSet fibers (ENNReal-valued,
      no per-window finiteness needed; empty = 0 correctly).
  N_off-nearline(I, eps): YES - encard of the fiber intersected with
      offLineZeroSet (committed, = re <> 1/2) and {|re - 1/2| < eps}.
  A(I) (the frame ratio of DISTINCT on-line ordinates, 1360 s4):
      NO-CHEAP. Two candidate formalizations, both rejected:
   (a) GAP SHADOW: A_gap := min-gap-of-ordinates / W, with
       sInf ∅ := 0. Rejected: without a local-finiteness input for
       zero sets, an INFINITE gap set inside a window can have
       sInf = 0, so a well-spread window misreads as fully clustered;
       and single-ordinate windows get A = 0 = maximum clustering,
       the exact opposite. (The F7 void-baseline lesson again:
       definitions on possibly-empty sets need their boundary read
       checked before the name is used.)
   (b) ENERGY REALIZATION: the prolate/frame ratio of 1353 s5's
       spread limb. That IS the L2a/L2c science (weeks-scale), not a
       definition.
      Decision: state TargetA2 as a SCHEMA in an uninterpreted spread
      function A : Int -> Real with 0 <= A <= 1 box available as a
      hypothesis where needed. The schema then machine-checks exactly
      two things: the RH-side collapse, and the residual = A > 0
      margin - see s3.

## 2. LOCKED statements (leaf Dev/C1TargetA2.lean)

Reuse (imported, never restated): windowSet, windowIndex, windowSet_mem
(1363 brick); onLineZeroSet, offLineZeroSet (C1SpectralOnlineSplit);
sourceNontrivialZeroSet (CC20YoshidaNearZeros).

Definitions (all new):

    windowTotalCount      (W : Real) (k : Int) : ENNReal
      := Set.encard (windowSet W k)
    windowOnLineCount     (W : Real) (k : Int) : ENNReal
      := Set.encard (windowSet W k ∩ onLineZeroSet)
    windowNearLineOffCount (W eps : Real) (k : Int) : ENNReal
      := Set.encard (windowSet W k ∩ offLineZeroSet
            ∩ {rho | |rho.1.re - 1/2| < eps})
    windowHeight          (W : Real) (k : Int) : Real := (k : Real) * W
    fstar                 (A : Real) : Real := A / (A + 2)
    targetA2Schema (W : Real) (T1 eps : Real) (A : Int -> Real) : Prop :=
      ∀ k : Int, windowHeight W k ≥ T1 →
        (1 : ENNReal) ≤ windowTotalCount W k →
        windowNearLineOffCount W eps k <
          ENNReal.ofReal (fstar (A k)) * windowTotalCount W k

Theorem/lemma names (locked): fstar_nonneg (A >= 0 -> fstar A >= 0),
fstar_zero (fstar 0 = 0), fstar_lt_one (A >= 0 -> fstar A < 1),
fstar_mono (0 <= A -> A <= B -> fstar A <= fstar B),
windowOnLineCount_le_total, windowNearLineOffCount_le_total,
nearLineOffCount_eps_mono (eps1 <= eps2 -> count(eps1) <= count(eps2)),
sourceRH_windowNearLineOffCount_zero
  (hRH : RHDefinitionBridge.standard.SourceRH) : all near-line off
  counts vanish (proof via sourceCriticalLine_to_mathlib),
sourceRH_targetA2_margin_reduction: under SourceRH, targetA2Schema
follows from the positivity margin (∀ k at height, 1 <= total ->
0 < fstar (A k)) - the residual content, named.

## 3. What this brick IS and IS NOT (rails, locked)

IS: the enemy's counting frame in the register; a machine-checked
    proof that under RH the off-line-near-line counts are ZERO, and
    that the ONLY remaining content of the A2-shape under RH is the
    strict positivity margin A > 0 at non-void windows (which - note
    - is NOT known unconditionally even from RH without the frame
    side; that is precisely the 1353 SPREAD limb, so the reduction is
    a MAP result, not a shortcut).
IS NOT: a statement that TARGET-A2 is provable, formalized, or even
    fully formulable yet (A uninterpreted by adjudication s1(b)); a
    contribution to the contest inequality (T4/B4.1 handle that);
    any inequality about zeta zeros beyond definitional monotonicity.
REGISTER HONESTY (law-42 + F5): the strict '<' in targetA2Schema is
    guarded by "1 <= windowTotalCount" - the F7 void-window amendment
    applied PRE-DIGIT to 1360 s4's prose ("empty window: 0 < 0 fails"
    is a real defect of the unguarded reading, fixed before any
    statement existed in code; the 1360 box itself is untouched
    history).

## 4. Acceptance contract (locked now)

Leaf Dev/C1TargetA2.lean + audit Dev/C1TargetA2Audit.lean (#print
axioms, fully qualified, no comments; expected: three standard
axioms, Data.attempt prohibited); batch = next free id at launch;
footer-sentinel acceptance; post-green byte-identity; no post-build
edits to locked statements.

## 5. Next actions

1. Build the leaf via the fast mirror loop; launch official batch.
2. On green: 1366 outcome ledger + register-line updates.
3. The 1357 owner card is unchanged otherwise; the only formal work
   left that needs no owner funding is L2c's realization - now named
   and priced at 1365 s1(b).
