# Record 1368 (OUTCOME) - H2 corridor brick GREEN, batch 1560: the wall now has a Lean signature, and its sufficiency is machine-checked

```text
+---------------------------------------------------------------------+
| What it is: batch 1560 compiled Dev/C1H2Corridor.lean + audit,      |
| zero errors, eight [propext, Classical.choice, Quot.sound] prints.  |
| The 1350 H2 skeleton is now a register object: windowMassBalance    |
| is the single named bridge, and the leaf PROVES that any instance  |
| of it (pure-counting or spread-carrying A2 form) discharges the     |
| gate and yields SourceRH through the committed d767a1d corridor.    |
| Why it matters: the claim "the wall is exactly L2/C6" - stated as   |
| prose in 1363/1366 - is now itself machine-checked: every link of   |
| the corridor outside hBridge is a proved theorem in this register.  |
| What it does NOT mean: no hBridge instance is claimed to exist;     |
| per 1353 the count-only instance is registered DEAD-DIRECTION       |
| (cluster configurations defeat it 70-146x); RH NOT claimed.         |
+---------------------------------------------------------------------+
```

## 1. Green evidence (raw, from the batch log)

```text
RESOURCE_DECISION class=normal lock=shared requested=auto
RESOURCE_SNAPSHOT available_gib=34.61 available_percent=98.2 load_per_cpu=0.04 cpus=16
RESOURCE_REASON focused warm Lake build: 2 explicit target(s)
RESOURCE_RESULT exit=0 log=build-logs/1560_h2_corridor.log (repository build-log directory)
Build completed successfully (3715 jobs).
grep -c error   -> 0
grep -c sorryAx -> 0
```

The eight axiom prints (lines 15-22 of the audit leaf), verbatim:

```text
'fstar_one'                             [propext, Classical.choice, Quot.sound]
'noMajority_eps_mono'                   [propext, Classical.choice, Quot.sound]
'noMajority_height_mono'                [propext, Classical.choice, Quot.sound]
'qw_nonneg_of_windowMassBalance'        [propext, Classical.choice, Quot.sound]
'sourceRH_of_windowMassBalanceBridge'   [propext, Classical.choice, Quot.sound]
'sourceRH_of_countBridge'               [propext, Classical.choice, Quot.sound]
'sourceRH_of_A2Bridge'                  [propext, Classical.choice, Quot.sound]
'sourceRH_windowMassBalance'            [propext, Classical.choice, Quot.sound]
```

(names above abbreviated to the `C1H2Corridor.` tail; the log carries
the fully qualified forms.)

Post-green byte-identity: sha256 `5a1ceb01...` (leaf) and `ee89ad5b...`
(audit) match the working tree exactly; locked statements untouched
after build. Law-42 order: 1367 design + source committed at 1a05f89
BEFORE the log existed; this record follows the log.

## 2. The corridor, as the register now holds it

```text
   noNearLineMajority(W,eps,T1)          targetA2Schema(W,T1,eps,A)
   = schema at A = 1, f*(1) = 1/3        (A = interpreted spread level)
        |                                   |
        | hBridge_count  [1353: DEAD DIR]   | hBridge_A2   [LIVE LANE]
        v                                   v
              windowMassBalance(g,W)  =  forall k,
                  0 <= windowOnLineMass g W k + windowOffLineMass g W k
        |
        | qw_nonneg_of_windowMassBalance   [PROVED: qw_window_assembly + tsum_nonneg]
        v
   (forall g, member g -> 0 <= qw g)
        |
        | weilCriterion_iff_sourceRH.mp    [committed, d767a1d]
        v
   RHDefinitionBridge.standard.SourceRH  ->  (tower)  RH

   positive control (proved, no hypothesis):
   SourceRH -> windowMassBalance(g,W) for every g,W
```

Interpretation, one line each:
- The sufficiency direction is CLOSED: `sourceRH_of_windowMassBalanceBridge`
  says one function - from the counting/balance hypothesis to the
  per-window balance, uniform on the triple-vanishing class - turns
  the wall into RH. Its type is the C6 charter's formal target.
- The positive control shows the corridor aims at a TRUE conclusion
  (at the RH endpoint every window balances trivially: off-line terms
  indicator-vanish, on-line terms are pointwise nonnegative).
- 1353's asymmetry verdict is now a rail INSIDE the register (the
  count-form theorem carries it in its docstring), not folklore.

## 3. Iteration ledger (4 compile rounds, all pre-green)

- Names needing qualification/fixing in this import chain:
  `weilCriterion_iff_sourceRH` lives under the `C1WeilCriterionEquivalence`
  namespace (not open by default); `spectralTerm` needs
  `open C1SpectralWeil`; `sourceNontrivialZeroSet` is a `Set ℂ` - as a
  binder it is the subtype, so field access is `rho.1` and RH applies
  as `hRH rho.1 rho.2` (no `.isNontrivial` field).
- `Set.indicator_eq_zero_of_not_mem` and `Set.indicator_of_not_mem` are
  ABSENT in this fork; the working shape is
  `classical; rw [Set.indicator_apply, if_neg hn, Complex.zero_re]`
  (indicator_apply carries a `[Decidable _]` instance argument that
  needs the classical context). `Set.indicator_of_mem` EXISTS (h_on
  compiled first try).
- `tsum_congr` + `tsum_zero` rewrote the windowed off-line mass to 0
  without further ceremony; `add_zero` closed the balance line.
- The two corridor theorems and monotonicities compiled as written
  (first try), confirming the 1366/1363 bricks snap together exactly
  as 1367 s1 anchored them.

## 4. Next actions

1. The owner card's option B can now be quoted as a LEAN TYPE: the C6
   charter = construct `hBridge` (spread form), i.e.
   `∀ g, member g -> targetA2Schema W T1 eps A -> windowMassBalance g W`
   for an interpreted `A` (1365 s1(b): the prolate/frame energy ratio).
   This is the only lane that moves RH toward the stop word.
2. Register-side, the attack inventory is now complete: 1363
   bookkeeping + 1366 counting frame + 1368 corridor signature.
   No further zero-analysis formal work is known; the honest queue is
   B (wall), C (1355 deep pass), D/E (harvest).
3. Stop word unchanged (1358 s4): "RH proven" is earned only by a
   green Lean artifact discharging the gate from the three standard
   axioms. Nothing today does - what today does is name the exact
   shape the certificate must have.
