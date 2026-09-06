# Record 1218 - consumption-chain regeneration against the true (2,8) gate boxes

Pre-registration.  Committed BEFORE any pipeline run (law 42).  Status:
REGISTERED.  Consumers: records 1216, 1217 (landed boxes), 1115/1118/1119
(committed chain being re-pointed).  No P2, no SourceRH, no RH.

## 1. Why

Record 1214 (F1) showed the committed 1112 M box for the class (2,8)
chain is a degenerate point box in the arch+prime convention: its
mixed-parity entries sit at about -0.35 while the TRUE gate matrix has
mixed-parity entries EXACTLY zero (record 1215 D1,
`gateMatrix_zero_of_odd`, landed 05bb009).  The committed
`q28_hbox_of_baseMomentBounds` hypothesis
(`MLo_q28 i j <= M_true i j <= MHi_q28 i j`) is therefore UNSATISFIABLE
for the true gate matrix at mixed parity: the committed q28 chain is
formally green but analytically dead.

Record 1217 landed the replacement: certified rational boxes
`MLo_q28M / MHi_q28M` around the TRUE gate matrix (mixed entries exact
`[0,0]` owned by D1; same-parity widths `<= 2.395e-13`), with
falsifier (b) PASSED (whitened top + inflation `-1.433227e-06 <=
U - 1e-8`, margin ~38x) and a same-parity hypothesis
`q28_hboxM_of_sameParity` that awaits the entrywise envelope campaign.

This record re-points the q28 consumption chain (whitened ingestion,
T-box, pull-through, headline) onto the true boxes, so that after the
entrywise campaign lands, the ENTIRE chain discharges.

## 2. Inputs (all committed, byte-frozen)

```text
docs/proofs/1112_cert.json              class (2,8): G_lo/G_hi, R_mid,
                                        U_outward  (G side used VERBATIM)
docs/proofs/1217_m_boxes_cert.json      entries i,j: lo/hi (dyadic 2^72),
                                        whitened_check.pass == True
ConnesWeilRH/Dev/C1WindowRationalIngestQ28.lean    Q28.U/G/R/K/V/W + hD/hKV/
                                        hWR/hclosure/hPencil data
ConnesWeilRH/Dev/C1HboxRationalData.lean  Hbox def, GLo_q28/GHi_q28,
                                        radG_q28, absK_q28, hrevG_q28,
                                        hsymRadG_q28, habsK_q28
ConnesWeilRH/Dev/C1GateMatrixBoxData.lean  MLo_q28M/MHi_q28M,
                                        q28_hboxM_of_sameParity
ConnesWeilRH/Dev/C1TboxPullthrough.lean   generic tbox_of_identities
ConnesWeilRH/Dev/C1GateLevelTransfer.lean  qform_nonneg_whitenedBox,
                                        ratio_headline, absolute_headline
ConnesWeilRH/Dev/C1Q28ClassGramIntervalTransfer.lean
                                        q28_classGram_bounds_of_baseMomentBounds
                                        (G side from I_0/I_2, UNCHANGED)
ConnesWeilRH/Dev/C1ConcreteClassMomentCertificate.lean
                                        q28_baseMoment_bounds_of_concrete_certificate
                                        (I_0/I_2, UNCONDITIONAL, landed 1145)
```

U is INHERITED (`U = Q28.U = U_outward[1]` of the 1112 class (2,8)
bundle): the 1217 falsifier (b) verified the box midpoints against the
SAME U with margin ~38x, and U is an input of the committed Q-module,
not a free knob of this record.

## 3. Machinery

Exact-Q (stdlib `fractions.Fraction`) forks of the record-1115
pipeline; json bundles are the only numeric inputs.

```text
1218_build_bundle.py      builds 1218_cert_q28.json: the 1112 class-(2,8)
                          bundle with M_lo/M_hi replaced by the 1217
                          dyadic boxes (mixed = exact "0").
                          Asserts: G/R/U byte-equal to 1112; M boxes
                          equal the 1217 entries exactly; 1217
                          whitened_check pass; lo <= hi everywhere.
1218_preprocess_q28.py    fork of 1115_rational_ingestion_preprocess.py,
                          single class.  Emits 1218_qchain_q28.json.
                          REGRESSION GATE: mid_G/rad_G/R/K/V/W must be
                          BYTE-EQUAL to the committed 1115_qchain.json
                          q28 entry (only the M side may move).
1218_generate_qmodule.py  emits ConnesWeilRH/Dev/
                          C1WindowRationalIngestQ28M.lean: Q28M.M/Dc/L/d
                          + hDtwo/hPencil only (U/G/R/K/V/W + hclosure
                          reused from Q28 by import).  Exact-Q
                          generation-time asserts mirror every emitted
                          norm_num identity.
1218_generate_hbox_m.py   emits ConnesWeilRH/Dev/
                          C1HboxRationalDataQ28M.lean: radM_q28M,
                          Lam_q28M, absLam_q28M, DredRad_q28M, radp_q28M
                          + hsymRadM/hrevM/habsLam/hLamL/hLLam/hDredRad/
                          hRadp.  M-side reverse containment ties
                          Q28M.M +/- radM_q28M to
                          C1GateMatrixBoxData.MLo_q28M/MHi_q28M.
                          G-side data (radG_q28, GLo_q28, GHi_q28,
                          absK_q28, hrevG_q28, hsymRadG_q28, habsK_q28)
                          reused from C1HboxRationalData by import.
1218_generate_classes_m.py  emits ConnesWeilRH/Dev/
                          C1GateLevelTransferClassesQ28M.lean:
                          dd_q28M, hradpos_q28M, hslack_q28M,
                          whitenedBox_q28M, mu_q28M (= -Q28.U),
                          ratio_q28M, absolute_q28M.
```

Hand-written modules (new files; no committed module is edited):

```text
ConnesWeilRH/Dev/C1TboxPullthroughQ28M.lean
  tbox_q28M       via the COMMITTED generic tbox_of_identities
  tbox_true_q28M  Hbox GLo_q28 GHi_q28 MLo_q28M MHi_q28M (Gt Mt)
  absolute_true_q28M
ConnesWeilRH/Dev/C1Q28MEntrywiseBinding.lean  (capstone)
  q28_hbox_1218_of_sameParity:
      hsp (20 same-parity entrywise facts, i + j even)
      -> Hbox GLo_q28 GHi_q28 MLo_q28M MHi_q28M
           (classGramMatrix 2 _) (gateMatrix (classTestFamily 2 _))
      via q28_hboxM_of_sameParity (M side, D1 closes mixed parity)
      + q28_classGram_bounds_of_baseMomentBounds
        (G side, from the LANDED I_0/I_2 concrete certificate)
      + hbox_of_classGramBounds.
  q28_absolute_1218_of_sameParity: hsp + representation/normalization
      slots -> ICgate <= -mu_q28M.  THE 1218 HEADLINE: the whole
      consumption chain reduced to the 20 same-parity entrywise facts.
ConnesWeilRH/Dev/C1Q28MEntrywiseBindingAudit.lean
  standard axiom audit + statement-form examples.
```

## 4. Falsifiers (any one fires -> ABORTED-UNINFORMATIVE, report, exit)

```text
F1  bundle: any 1217 field mismatch (G/R/U vs 1112, M vs 1217,
    whitened_check.pass != True)                       -> exit 3
F2  preprocess: any exact-Q assert (RREF rank/identity, LDL positive
    pivots, closure identities)                        -> script assert
F3  regression gate: mid_G/rad_G/R/K/V/W not byte-equal to the
    committed q28 qchain entry                         -> exit 4
F4  feasibility: min exact-Q slack <= 0 (dd_q28M vs radp_q28M kernel
    charges).  NOTE (honest risk): the 1217 falsifier (b) certified
    negativity in the MOMENT metric; the slacks live in the LDL of
    K' * (U*G - M) * K.  The mixed-parity M shift (-0.35 -> 0) moves
    Dred by O(0.1); slack positivity is NOT pre-certified - the run
    decides.  RED here means the true boxes do not feed the committed
    T-box shape unchanged and the record claim dies               -> exit 2
F5  generation-time identity assert in any emitter    -> exit 1, no module
F6  Lean build: any error / sorryAx / ofReduceBool in the new modules
```

Widths are never hand-widened (1097 protocol).  No committed module is
edited; the old q28 chain remains exactly as committed.

## 5. Acceptance

```text
A1  1218_cert_q28.json + 1218_qchain_q28.json committed with min
    slack > 0 and the regression gate PASS line
A2  five new Lean modules build green in WSL (footer, 0 error,
    0 sorryAx, 0 ofReduceBool)
A3  standard axiom lists for the capstone headline and the tbox_true
    theorem (only the approved standard axioms)
A4  min slack reported numerically in the verdict record
A5  hygiene scan before push; upstream read-back after
```

## 6. Scope

Class (2,8) only.  The q38/q48 chains stay exactly as committed (their
M-side boxes carry the same 1214 fracture; regenerating them is a
mechanical follow-up once the entrywise campaign covers those classes'
G sides).  RH NOT claimed.

## 7. Amendment (2026-09-07, committed BEFORE the first green run)

F1 as registered asserted `mixed box == exact [0, 0]` against the 1217
CERT JSON.  First launch fired F1 at (0,1):
`[-527801769/4722366482869645213696, +527801769/4722366482869645213696]`.
Not a data problem: the 1217 engine writes every box as
`mid +/- outward(budget)` uniformly (mixed mids are ~1e-47, budget
~1.1e-13), while the COMMITTED Lean data (C1GateMatrixBoxData) and D1
ownership use EXACT [0, 0] mixed boxes.  Amendment: F1 checks mixed
CONSISTENCY instead (`|mid| <= budget` and `0 in box`), and the bundle
EMITS exact `0` for mixed endpoints so the bundle M data is
entry-identical to the committed Lean data the Lean reverse
containment will be tied to.  Same-parity boxes unchanged.

## 8. Amendment 2 (2026-09-07, committed BEFORE the emitter runs)

The 1217 engine rounds each entry independently outward, so the
bundle's M radius matrix is not EXACTLY symmetric: measured asymmetry
1.0588e-22 on exactly four entries ((3,5), (3,7) and transposes) - a
last-bit dyadic artifact.  The Lean chain needs `hsymRadM`
(`tbox_of_identities` hypothesis `hradMsym`), and the parent 1119
pipeline asserted `rad_M symmetric` as a generation check.  The fork
therefore symmetrizes rad_M by ENTRYWISE MAX
(`rad_M[i][j] = rad_M[j][i] = max(...)`, i < j) BEFORE the downstream
Dred_rad / radp / slack computation - the same "the box side inherits
the asymmetry as radius correction" principle the parent registered
for the D centers (1115 registered finding).  Conservative: radii
only grow; reverse containment is preserved; slack impact ~1e-22
against a 1.9e-8 min slack.  The center `M` stays as computed
(asymmetric at 5.7e-18 - allowed; the generic T-box needs no symmetry
hypothesis on the center, only on the radii).
