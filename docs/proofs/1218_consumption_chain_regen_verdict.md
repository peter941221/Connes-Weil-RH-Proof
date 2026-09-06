# Record 1218 - consumption-chain regeneration VERDICT

Date: 2026-09-07.  Status: LANDED.
Prereg: 1218_consumption_chain_regen_preregistration.md (committed
a51aa58 before any run; amendments sec. 7/8 each committed BEFORE the
affected run, law 42).  Consumers: records 1215/1216/1217, 1219.
No P2, no SourceRH, no RH.

## 1. Verdict

The class (2,8) consumption chain is re-pointed at the TRUE gate
matrix boxes (record 1217) and is GREEN end to end:

```text
exact-Q feasibility   F4 GREEN: five slacks strictly positive,
                      min slack = 1.874810e-08
regression gate       F3 PASS: mid_G/rad_G/R/K/V/W byte-equal to the
                      committed 1115 q28 entry (only M moved)
headline              q28_absolute_1218_of_sameParity:
                      hsp (20 same-parity entrywise facts)
                        + representation/normalization slots
                      -> ICgate <= -mu_q28M
```

The committed old chain's `MLo_q28/MHi_q28` hypothesis was
UNSATISFIABLE for the true gate matrix (1214 fracture: mixed-parity
point boxes at ~-0.35 vs true exact 0); the new chain consumes
`MLo_q28M/MHi_q28M` (mixed entries exact zeros, owned by D1) and
carries the same-parity hypothesis that record 1219 discharges.

## 2. Slack comparison (old point-box chain vs new true-box chain)

```text
i    dd_old       slack_old    dd_new       slack_new    delta
0    2.012361e-06 2.012241e-06 2.012361e-06 2.012358e-06 +5.9e-12
1    4.989595e-06 4.989322e-06 4.989595e-06 4.989589e-06 +2.7e-11
2    4.446730e-07 4.442652e-07 4.446730e-07 4.446641e-07 +4.0e-10
3    1.837429e-07 1.835223e-07 1.837429e-07 1.837383e-07 +2.2e-10
4    1.875333e-08 1.851287e-08 1.875333e-08 1.874810e-08 +2.4e-10
```

The TRUE boxes give MORE margin than the old point boxes (the mixed
~-0.35 junk removed from Dc is benign): min slack improved
1.851287e-08 -> 1.874810e-08 (+1.3%).

## 3. Run ledger

```text
prereg a51aa58   preregistered (F1 mixed-exact-zero assert as written)
run 1  exit 3    F1 fired at (0,1): the 1217 CERT JSON stores
                 mid-+/-budget boxes at mixed parity; the committed
                 LEAN data and D1 ownership use exact [0,0] -> prereg
                 sec. 7 amendment (consistency check; bundle emits
                 exact zeros), committed BEFORE the rerun
run 2  GREEN     bundle + exact-Q preprocess: F1 PASS, F3 PASS,
                 F4 GREEN (min slack 1.874810e-08); the F5 checks of
                 the three emitters PASS
build1  FAILED   hD seq-shape "No goals" (new M has exact-zero mixed
                 entries, simp closes those foci; the parent's M had
                 nonzero mixed entries) -> emitter to focus shapes
build2  FAILED   RED-4 heartbeat: hD/hDc whnf timeout at default
                 200000 -> qmodule emitter raised budgets + STAGED
                 pencil identities mirroring the parent (hDK/hKDK/
                 hLd/hLdLt + hPencil rw composition)
build3  FAILED   hLdLt seq-shape "No goals" -> all staged identities
                 to focus shapes
build4  FAILED   classes-Q28M: ratio_headline/absolute_headline
                 unknown -> open the committed classes module
build5  FAILED   hbox-Q28M "unterminated comment": the docstring text
                 "+/-" is a NESTED-COMMENT opener in Lean 4 -> all
                 "+/-" in emitted comment text replaced
build6  FAILED   tbox fork: tbox_of_identities unknown -> open the
                 committed pullthrough module
build7  FAILED   capstone: two missing opens (concrete certificate +
                 classes-Q28M namespaces)
build8  FAILED   E1: Set open missing; capstone: classGram-transfer
                 namespace open missing
build9  FAILED   E1: `Ioo (-2 * a)` vs `-(2 * a)` NOT defeq (numeral
                 placement); audit: Q28M namespace path + open
build10 GREEN    build-logs/1218-q28m-build10.log: footer
                 "Build completed successfully (3707 jobs)",
                 0 `^error:`, 0 sorryAx, 0 ofReduceBool, ALL SEVEN
                 standard axiom lists
                 [propext, Classical.choice, Quot.sound]
```

No hand-widening anywhere; every retirement kept its log (law 42 +
1097 discipline).

## 4. Landed artifacts

```text
docs/proofs/1218_build_bundle.py          bundle builder (F1)
docs/proofs/1218_cert_q28.json            the (2,8) bundle: G/R/U
                                          byte-equal 1112 + 1217 M
docs/proofs/1218_preprocess_q28.py        exact-Q fork (F3/F4)
docs/proofs/1218_qchain_q28.json          1-class qchain, min slack
                                          1.874810e-08
docs/proofs/1218_generate_qmodule.py      -> C1WindowRationalIngestQ28M
docs/proofs/1218_generate_classes_m.py    -> C1GateLevelTransferClassesQ28M
docs/proofs/1218_generate_hbox_m.py       -> C1HboxRationalDataQ28M
ConnesWeilRH/Dev/C1WindowRationalIngestQ28M.lean   GENERATED
ConnesWeilRH/Dev/C1GateLevelTransferClassesQ28M.lean GENERATED
ConnesWeilRH/Dev/C1HboxRationalDataQ28M.lean       GENERATED
ConnesWeilRH/Dev/C1TboxPullthroughQ28M.lean        hand fork
ConnesWeilRH/Dev/C1Q28MEntrywiseBinding.lean       capstone
ConnesWeilRH/Dev/C1Q28MEntrywiseBindingAudit.lean  axioms + examples
```

No committed module is edited; the old q28 chain remains exactly as
committed.

## 5. Build evidence

build-logs/1218-q28m-build10.log: footer "Build completed
successfully (3707 jobs)", 0 `^error:`, 0 sorryAx, 0
ofReduceBool, and the standard axiom lists
`[propext, Classical.choice, Quot.sound]` for ALL SEVEN audited
declarations: C1WindowRationalIngest.Q28M.top,
C1GateLevelTransferClassesQ28M.hslack_q28M,
C1HboxRationalDataQ28M.hrevM_q28M,
C1TboxPullthroughQ28M.tbox_true_q28M,
C1TboxPullthroughQ28M.absolute_true_q28M,
C1Q28MEntrywiseBinding.q28_hbox_1218_of_sameParity,
C1Q28MEntrywiseBinding.q28_absolute_1218_of_sameParity.
Record 1219 E1 (C1GateEntryCorrelation) built in the same run.

## 6. Honest scoping

Class (2,8) only; q38/q48 chains unchanged (their M side still carries
the 1214 fracture; mechanical follow-up once 1219 covers their G
sides).  The chain is conditional on `hsp` (20 same-parity entrywise
facts) - record 1219's E2-E5 discharge them.  The representation and
normalization slots (hrep/hker/hnorm) remain named hypotheses exactly
as in the committed chain.  RH NOT claimed.
