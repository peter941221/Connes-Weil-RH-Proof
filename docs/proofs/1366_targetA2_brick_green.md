# Record 1366 (OUTCOME) - TARGET-A2 counting-frame brick GREEN, batch 1559: the enemy now has a Lean name; residual = the A > 0 spread margin

```text
+---------------------------------------------------------------------+
| What it is: batch 1559 compiled Dev/C1TargetA2.lean + audit with     |
| zero errors and nine [propext, Classical.choice, Quot.sound]        |
| prints - the 1365 locked statements are now machine-checked facts.   |
| Why it matters: the direct-attack enemy (1360 s4 TARGET-A2) is      |
| INSIDE the register; the brick also pins, with proofs, exactly what |
| is trivial under RH (off-near-line counts vanish) and what is NOT   |
| (the strict positivity margin A k > 0 at non-void windows - the     |
| 1353 s5 SPREAD limb, now named in theorem statements).              |
| What it does NOT mean: RH is not claimed; A remains uninterpreted   |
| (1365 s1 adjudication stands); no analysis was used or produced.    |
+---------------------------------------------------------------------+
```

## 1. Green evidence (raw, from the batch log)

```text
RESOURCE_DECISION class=normal lock=shared requested=auto
RESOURCE_SNAPSHOT available_gib=34.62 available_percent=98.3 load_per_cpu=0.02 cpus=16
RESOURCE_RESULT exit=0 log=build-logs/1559_l2c_target_a2.log (repository build-log directory)
Build completed successfully (3714 jobs).
grep -c error  -> 0
```

The nine axiom prints, verbatim (all three standard axioms, zero sorryAx):

```text
'C1TargetA2.fstar_nonneg'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'C1TargetA2.fstar_zero'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'C1TargetA2.fstar_lt_one'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'C1TargetA2.fstar_mono'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'C1TargetA2.windowOnLineCount_le_total'    depends on axioms: [propext, Classical.choice, Quot.sound]
'C1TargetA2.windowNearLineOffCount_le_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'C1TargetA2.nearLineOffCount_eps_mono'     depends on axioms: [propext, Classical.choice, Quot.sound]
'C1TargetA2.sourceRH_windowNearLineOffCount_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'C1TargetA2.sourceRH_targetA2_margin_reduction'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

Post-green byte-identity: `sha256` of the mirror copies of
C1TargetA2.lean (e085dfdb...) and C1TargetA2Audit.lean (5a26ef1d...) match
the working tree exactly. Locked statements were not edited after build.

## 2. What the register now contains (chain state)

```text
  TARGET-A2 (1360 s4)      "N_off-nearline(I) < f*(A(I)) * N(I) above T1"
        | named as
        v
  targetA2Schema           Lean def, F7-void-guarded (1363 brick windows)
        | two proved faces
        +-- sourceRH_windowNearLineOffCount_zero     (RH side: LHS = 0)
        +-- sourceRH_targetA2_margin_reduction       (residual = 0 < fstar (A k),
        |                                             i.e. A k > 0: the SPREAD limb)
        v
  L2 / C6 science (UNBUILT, owner-gated)             the only wall-facing lane
        v
  T4 -> B4.1 gate -> weilCriterion_iff_sourceRH (d767a1d) -> RH
```

Honesty rail (locked in 1365 s3, unchanged): the margin reduction is a
MAP result. Even assuming RH, `A k > 0` at every non-void window is not
known unconditionally without the frame (energy) side - that is the
1353 placement finding restated inside a theorem type.

## 3. Iteration ledger (6 compile rounds, all pre-green; law-42: design committed with source at e335308, log came after)

Fork API ground truth learned (candidates for AGENTS 7b):

- `exact_mod_cast` is a TACTIC in this fork: `exact_mod_cast h` at tactic
  position compiles; `refine exact_mod_cast (..)` fails ("Unknown
  identifier"), and the bare term `mod_cast` does not exist as a tactic
  either. Pattern that works: build the un-coerced fact as a `have`, then
  `exact_mod_cast <lemma> <have>` in tactic position.
- `Set.encard : Set α -> ℕ∞` (not ENNReal): definitions annotated
  `: ENNReal` insert coercion nodes; `exact_mod_cast
  Set.encard_le_encard hsub` closes `↑(encard s) ≤ ↑(encard t)` goals.
- `Set.eq_empty_of_forall_not_mem` and `Set.eq_empty_iff_forall_not_mem`
  are ABSENT in this fork's import chain; use
  `Set.not_nonempty_iff_eq_empty.mp` (direction: `.mp` is
  ¬Nonempty -> s = ∅; `.mpr` is the converse) with a pattern-matching
  lambda `fun ⟨x, hx⟩ => by ...`, then
  `exact_mod_cast Set.encard_eq_zero.mpr hempty`.
- `ENNReal.ofReal_pos.mpr` + `mul_le_mul_of_nonneg_left` + `le_of_lt`
  work as stated on ENNReal; the generic `zero_le _` mis-elaborates in
  this chain (resolved to a proof term, "Function expected") - pass an
  explicit `le_of_lt h` instead.
- `gcongr` closed the fstar_mono side goal outright; the appended
  `<;> nlinarith` was dead code (two "never executed" warnings, dropped).
- Launcher trap recurrence (toolbox law): `wsl.exe -c 'cp ... && nohup
  ... &'` backgrounds the WHOLE AND-chain; when the wsl.exe session
  exits, the chain dies mid-way (the audit file never got copied).
  Sync and launch must be SEPARATE wsl.exe invocations, or the launch
  must run under the harness background mechanism.

## 4. Next actions

1. The formal corridor is exhausted at the register level: every
   statement that needs no new analysis is now proved (L1 bookkeeping,
   1363; A2 counting frame, 1366). The remaining lane is owner-gated:
   L2a localized sampling / L2b sinc^2 gluing / L2c count-to-energy
   (1365 s1(b)) is the only wall-facing science, priced there.
2. Owner card 1357 (weights updated): B = commission L2/C6 charter;
   C = 1355 deep pass; D = #9-style thermometer continuation;
   E = harvest-only. A2-frame brick lands as an additional harvest
   deliverable of the 开干 wave.
3. Stop word unchanged (charter 1358 s4): only a Lean artifact
   discharging the gate (or contestForm) from the three standard
   axioms with a green footer earns "RH proven". Nothing today does.
