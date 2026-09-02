# 1098 - the S2 absorbed-legality discharge (canonical primitive re-point)

Date: 2026-09-02.

Status: record 1097b fired H1-REJECTED / H2-CONFIRMED, so the pre-registered
mapping re-points the S2 producer primitive set and lands this brick. RH is
not claimed. Evidence labels follow map `004` section 1.

## 1. What the fork decided

Record 1096 discharged the record-1095 consumer contract to the single
primitive `targetProlateRemainderFactorHS` (A in Hilbert-Schmidt, equivalently
`Tr K_S < inf`).  That primitive is the RAW-F1 quantity class that record 1063
falsified in the model.  The 1097/1097b fork tested whether the committed
four-octave growth under-detects a bend at a certified deeper octave:

```text
+-----------------------------------------------+------------------+
| observable (record-1068 rig, family {2,3,5})  | deep-octave fate |
+-----------------------------------------------+------------------+
| raw trace Tr K_S (the A-in-HS class)          | 34.2696 -> 41.0499, |
|                                               | slope16x +0.335,    |
|                                               | no bend (H1 FIRES)  |
| p_hs = Tr(C^dag K_S C) = norm(A C)_HS^2  (a)  | slope8x -0.004, O(1)|
| l_tr1 = norm([C, K_S])_nuclear           (b)  | slope8x -0.022, O(1)|
+-----------------------------------------------+------------------+
```

The certification gates of 1097b all passed: the source-family trace stayed
flat at the fine octave (G-src, 1.36e-02), the coarse-dxi member of the deep
pair sat strictly above the fine member on every trace-class observable in
both families (G-brkt), and the coarse source excursion sat outside the
committed band (G-conf, 1.79e-01), identifying the coarse grid as the
artifact.  Verdict: the A-in-HS discharge route is CLOSED for continuum
scheduling (NUMERICAL guard at the 1063 standard); the canonical S2
primitive set is (a) the detector-absorbed factor in HS plus (b) the
commutator-remainder trace legality.

## 2. The brick

`ConnesWeilRH/Dev/C1ProlateRootCommutatorAbsorbedLegalityDischarge.lean`
(+ paired audit) lands the re-point:

- PRIMITIVE (a) `targetProlateDetectorAbsorbedFactorHS`:
  `Summable fun i => norm (A (C e_i))^2` - the detector-ABSORBED factor is
  Hilbert-Schmidt.  Its numerical witness is the committed record-1068
  positive sandwich `p_hs` 3.5661 -> 3.5356 over four octaves.
- PRIMITIVE (b) `targetProlateDetectorRootCommutatorTraceLegality`: the
  leaf's own S2 obligation - trace legality of the commutator remainder
  `C^dag . [C, K_S]`.  Its numerical witness is the committed record-1068
  nuclear norm `l_tr1` 1.3462 -> 1.2850; the bounded `C^dag` dressing costs
  only the fixed constant `norm C` on the model (`norm(C^dag T)_nuclear <=
  norm C * norm T_nuclear` for the true nuclear norm), so the O(1)
  measurement transfers to the dressed object up to that constant.
- `targetProlateDetectorAbsorbedPairData` + `_traceProduct_eq`: the pair
  data with both legs `A . C`, whose trace product is EXACTLY the right
  WITH-C-dagger summand `(A C)^dag . (A C) = C^dag . K_S . C` - so the
  right summand's diagonal along the global basis IS the (a) series, and
  `traceProduct_isTraceClassAlong` carries it with no sandwich argument.
- LAW-16 WIRING `...LeftSummand_eq_add`: `D . K_S = C^dag . K_S . C +
  C^dag . [C, K_S]`, that is `LeftSummand = RightSummand + Remainder`
  (the leaf's own decomposition, proved here by `abel` after the committed
  two-summand difference identity).
- HEADLINE `...SandwichedTermNuclearity_of_absorbedLegality`: the
  record-1095 consumer contract follows from (a) and (b) alone.  The
  record-1096 A-in-HS primitive is not used anywhere in the module.

Build evidence: `build-logs/1098_absorbed_build2.log`,
`Build completed successfully (3201 jobs)`, zero `error:` lines, and all
seven declarations print exactly `[propext, Classical.choice, Quot.sound]`
(zero `sorryAx`).  One iteration was needed: after
`simp only [comp_assoc, adjoint_comp]` the associativity normal form is
right-nested, so `A^dag . A` never appears as a subterm and
`adjoint_comp_self` cannot fire; an explicitly argumented
`rw [← comp_assoc A^dag A C]` re-associates the inner factor first.

## 3. What stays and what is demoted

- Record 1095 (`C1ProlateRootCommutatorPerTermNuclearityGlue`) stays the
  canonical consumer contract: the headline here TARGETS its
  `SandwichedTermNuclearity` unchanged, and its glue to the leaf is
  untouched.
- Record 1096 (`C1ProlateRootCommutatorSandwichedNuclearityDischarge`)
  is demoted to a VALID-BUT-UNSCHEDULABLE implication: its Lean content is
  correct (it was built green and its axioms are clean), but its primitive
  is the falsified quantity class, so no producer work may schedule it.
  Its doc carries the erratum block.
- Still owed after this brick (unchanged from the 1095/1096 ledger):
  (i) prove primitive (a) on the continuum carrier for the actual family
  (witness: committed p_hs O(1)); (ii) prove primitive (b) on the continuum
  carrier (witness: committed l_tr1 O(1)); (iii) owner transfer from the
  stand-in Gaussian root to the selected convolution root per owner.
