# Record 1367 (DESIGN + LOCKED STATEMENTS) - the H2 corridor formalized: the wall gets a Lean signature; per-window balance is the ONE missing bridge (pre-build lock, law 42)

```text
+---------------------------------------------------------------------+
| What it is: the paper H2 (1350, corrected by 1353) turned into      |
| register objects. Three named Props/theorems:                        |
|   windowMassBalance  = the per-window balance (leg L3's target),     |
|   noNearLineMajority = the H1/H2 counting hypothesis                 |
|                        (= targetA2Schema with A = 1, since           |
|                         f*(1) = 1/3 is EXACTLY H1's majority         |
|                         threshold), and                              |
|   sourceRH_of_*Bridge = machine-proved corridors: ANY bridge from    |
|                         counting/balance to windowMassBalance        |
|                         discharges the gate and hence SourceRH.      |
| Why: the direct-attack order. 1366 said the corridor is exhausted   |
| at register level; this record makes that claim machine-checkable:  |
| every link of the L1-L5 skeleton that is formal is proved formal    |
| here, and the ONLY unformal content is isolated as a single         |
| explicit hypothesis (the bridge). The C6 charter then has a Lean    |
| signature to aim at.                                                |
| What it does NOT mean: no bridge is claimed to exist. Per 1353 a    |
| bridge from PURE COUNTING (T6's hypothesis form) is NOT derivable   |
| (clustered configurations defeat count assembly); the survivable    |
| form is the spread-carrying A2 bridge (T7). RH NOT claimed.         |
+---------------------------------------------------------------------+
```

## 1. Anchors (committed, reused, never restated)

- `weilCriterion_iff_sourceRH` (d767a1d):
  `(∀ g : CompactLogTest, CC20VanishesOn C1.healthyCC20TestSpace
     cc20TripleFiniteVanishingSet g → 0 ≤ C1SameOwnerWeil.qw g) ↔
     RHDefinitionBridge.standard.SourceRH`; the `.mp` direction is the
  gate-to-SourceRH leg (constructor 1 = `sourceRH_of_all_vanishing_qw_nonneg`).
- `qw_window_assembly (g W)` (1363 T3):
  `qw g = ∑' k, (windowOnLineMass g W k + windowOffLineMass g W k)`.
- `windowOnLineMass / windowOffLineMass / windowSet` (1363),
  `targetA2Schema / fstar / nearLineOffCount_eps_mono` (1366).
- `onLineSpectralTerm = onLineZeroSet.indicator (spectralTerm ...)`,
  `offLineSpectralTerm = offLineZeroSet.indicator ...` (C1SpectralOnlineSplit
  :47-54); `spectralTerm_convolutionSquare_nonneg_of_onLine (g rho)
  (honline : rho.1.re = 1/2) : 0 ≤ (spectralTerm g.convolutionSquare rho).re`
  (C1SpectralOnlineNonneg :50-53).

## 2. LOCKED statements (leaf Dev/C1H2Corridor.lean, namespace
##    ConnesWeilRH.Source.C1H2Corridor)

Definitions:

    windowMassBalance   (g : CompactLogTest) (W : Real) : Prop :=
      ∀ k : Int, 0 ≤ windowOnLineMass g W k + windowOffLineMass g W k
    noNearLineMajority  (W eps T1 : Real) : Prop :=
      targetA2Schema W T1 eps (fun _ => 1)

Theorems (locked names):

    fstar_one                        : fstar 1 = 1/3
    noMajority_eps_mono (W) {eps1 eps2} (h : eps1 <= eps2) (T1) :
      noNearLineMajority W eps2 T1 -> noNearLineMajority W eps1 T1
    noMajority_height_mono {Ta Tb} (h : Ta <= Tb) (W eps) :
      noNearLineMajority W eps Ta -> noNearLineMajority W eps Tb
    qw_nonneg_of_windowMassBalance (g W) :
      windowMassBalance g W -> 0 <= C1SameOwnerWeil.qw g
    sourceRH_of_windowMassBalanceBridge (W) :
      (∀ g, member g -> windowMassBalance g W) -> SourceRH
    sourceRH_of_countBridge (W eps T1) :
      (∀ g, member g -> noNearLineMajority W eps T1 ->
         windowMassBalance g W) ->
      noNearLineMajority W eps T1 -> SourceRH
    sourceRH_of_A2Bridge (W eps T1) (A : Int -> Real) :
      (∀ g, member g -> targetA2Schema W T1 eps A ->
         windowMassBalance g W) ->
      targetA2Schema W T1 eps A -> SourceRH
    sourceRH_windowMassBalance (hRH : SourceRH) (g W) :
      windowMassBalance g W        [POSITIVE CONTROL: the balance Prop
        is true at the RH endpoint, so no bridge hypothesis is
        inconsistent with its conclusion]

where `member g` abbreviates `CC20VanishesOn C1.healthyCC20TestSpace
cc20TripleFiniteVanishingSet g` (written in full in the leaf, exactly
as at C1WeilCriterionEquivalence.lean:137-139).

Proof obligations declared in advance (law-42 transparency):
- qw_nonneg...: rw [qw_window_assembly]; exact tsum_nonneg h.  (2 steps)
- sourceRH_of_windowMassBalanceBridge: weilCriterion_iff_sourceRH.mp,
  discharged by the previous theorem pointwise.
- count/A2 bridges: composition only (apply the balance bridge to the
  composed hypothesis); T6 uses noNearLineMajority = schema(A≡1) by
  unfolding.
- sourceRH_windowMassBalance: per window k: offline mass = 0 (each
  indicator point vanishes under rho.1.re = 1/2; tsum_congr + tsum of
  zero) and online mass >= 0 (tsum_nonneg + Set.indicator_of_mem +
  spectralTerm_convolutionSquare_nonneg_of_onLine +
  sourceCriticalLine_to_mathlib).
- eps/height monotonicities: nearLineOffCount_eps_mono (1366) chained
  with lt_of_lt_of_le; height guard is restriction of a forall.

## 3. Rails (locked)

IS: the machine-checked map "per-window balance is the ONE missing
    bridge": legs L1/L2 of 1350 s3 are already committed-formal, L5 is
    a MODEL-level census, and L3/L4's surviving content appears here
    exactly as the type of hBridge / hA2.
IS NOT: a proof that any bridge exists (1353 says the pure-counting
    form CANNOT be discharged; only the spread-carrying A2 form is
    live, and its realization is the registered L2a/L2b/L2c science);
    new analysis; RH.
Honesty note on noNearLineMajority: 1350 s2's H1 counts ALL off-line
    zeros vs threshold 1/3; our Prop counts only NEAR-LINE off-line
    zeros (a weaker hypothesis to satisfy, stronger conclusion). The
    H2 statement itself (1350 s3) uses the ultra-near-line form, so
    the formalization matches H2; matching H1's all-off-line form
    would need an all-off-line count def (not taken: H1's own reading
    goes through the (star) contest which is the A2 route anyway).

## 4. Acceptance contract (locked now)

Leaf Dev/C1H2Corridor.lean + audit Dev/C1H2CorridorAudit.lean
(#print axioms, fully qualified; expected: three standard axioms each,
zero sorryAx); batch = next free id at launch; footer-sentinel
acceptance; post-green byte-identity; no post-build edits.

## 5. Next actions

1. Build via mirror loop; official batch; outcome record 1368.
2. If green: the C6/L2 charter target statement is this leaf's bridge
   type - hand it to the owner card as the formal ask.
3. Stop word unchanged (1358 s4).
