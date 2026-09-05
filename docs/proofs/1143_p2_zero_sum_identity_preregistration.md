# Record 1143 - P2 zero-sum identity audit (pre-brick B1 of map 005)

Date: 2026-09-05.  Status: pre-registration, committed BEFORE any build.

Consumer: the healthy-`CompactLog`, B5-shaped detector-specific semi-local
chain (map [`003`](../map/003_b1_b5_minimal_exit_route_selection.md)
freeze item 3/4); concrete consumer is the P2 producer design of map
[`005`](../map/005_p2_scalar_witness_zero_configuration_design.md) section 6
brick B1.  RH is not claimed; no sign theorem is asserted.

## 1. Scope

Statement-level identity audit only.  The brick pins, as named Lean
equations, the exact chain from the one-window Stage-B defect gate to the
spectral difference form, and the positive-form admission wall:

```text
ICgate(defect)  --1123-->  ICgate g.convSq - ICgate W.convSq
                --vanish-->  -qw g + qw W  =  qw W - qw g
                --Z3---->  spectralWeilValue W.convSq
                           - spectralWeilValue g.convSq
```

No new analytic content: every ingredient is a landed theorem (record 1123
`defectGate_singleton_eq_sub`, the `qw` vanishing readback in
`C1HealthyYoshidaDetector`, the `psi`/`qw` definitions in
`C1SameOwnerWeil`, and record Z3 `centerTwo_arithmetic_eq_spectral` in
`C1XiCenterTwoArithmeticAssembly:232`).  The brick composes them once so
that the Line-S verdict (delivered as docs/proofs/1144) cites named
equations instead of re-derivations.

## 2. Declarations (new module `C1P2DefectZeroSumIdentity` + `...Audit`)

Let `D g W` abbreviate
`ICgate (ICdefect g.convolutionSquare {()} (fun _ => W.convolutionSquare)
(fun _ => 1))` and `V t` abbreviate
`CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet t`.

```text
+----+--------------------------------------+------------------------------------------------+
| ID | Statement                            | Form                                           |
+----+--------------------------------------+------------------------------------------------+
| S1 | icgate_convolutionSquare_eq_neg_qw   | V F -> ICgate F.convolutionSquare = -qw F      |
| S2 | defectGate_eq_qw_sub                 | V g -> V W -> D g W = qw W - qw g              |
| S3 | defectGate_eq_spectralValue_sub      | V g -> V W -> D g W = SW W.convSq - SW g.convSq|
| S4 | defectGate_gt_add_mu                 | 0 < ICgate g.convSq -> ICgate W.convSq <= -mu  |
|    |                                      |   -> mu < D g W                                |
| S5 | defectGate_gt_add_mu_of_qw_negative  | V g -> qw g < 0 -> ICgate W.convSq <= -mu      |
|    |                                      |   -> mu < D g W                                |
+----+--------------------------------------+------------------------------------------------+
```

Notes:

* S1 is the equation form of the `hgate` step already proved inside
  `no_stageB_budget_of_qw_negative`; no vanishing input beyond `V F`.
* S3 consumes `qw_eq_psi_square` (rfl) and
  `centerTwo_arithmetic_eq_spectral F` (Z3, unconditional) for both tests.
* S4 needs NO vanishing: it is the positive-form wall behind record 1140's
  `False`.  S5 re-derives the `0 < ICgate g.convSq` input from the
  detector negativity exactly as 1140 does.
* Statement names may shift at implementation; any change is registered in
  the post-run addendum.  Argument orders follow the house style (test
  first, hypotheses after).

## 3. Proof routes (all one-liners by design)

```text
S1: unfold ICgate; linarith over the qw readback equation.
S2: rw [defectGate_singleton_eq_sub, S1(g), S1(W)]; ring.
S3: rw [S2]; transport each qw through qw_eq_psi_square + Z3; rw.
S4: rw [defectGate_singleton_eq_sub]; linarith.
S5: refine S4; unfold ICgate; linarith with the qw readback + hnegative.
```

Audit module: focused `#print axioms` on S1-S5 (expected exactly
`[propext, Classical.choice, Quot.sound]`), plus one G3 fidelity `example`
deriving the S3 form from explicit hypotheses.

## 4. Gates

```text
G1  Runner build of both targets green: footer "Build completed
    successfully (N jobs)" AND zero ^error: lines in the log.
G2  Every audited declaration prints exactly
    [propext, Classical.choice, Quot.sound]; zero sorryAx.
G3  The fidelity example compiles inside the audit module.
G4  Hygiene: no local paths, no private workflow artifacts, no mojibake
    in any committed file.
```

Falsifier: none registered - this is pure algebra over landed theorems.
If a statement does not typecheck as written, root-cause and register the
deviation in the addendum; no statement is weakened silently.

## 5. Downstream deliverable (separate record, not this build)

The Line-S verdict of map 005 section 4.1 will be issued as
docs/proofs/1144 citing S3/S5 + `no_stageB_budget_of_qw_negative`: for
EVERY admissible window (hcert), the defect gate exceeds `mu >= epsilon`,
so no channel decomposition of the spectral difference can re-derive the
budget `D g W <= epsilon <= mu`; Line S dies as stated without a probe
run (AGENTS rule 1: no substantively idle numerical experiment).  That
verdict changes map 005 section 4/6 only.
