# 1056 - F1 scope: the unit-scale semilocal crux is legal, and it is not plumbing

Date: 2026-08-30. Follows 1050, 1055, and the brick #1 landing `16b5f96`.

Status:

```text
RULING 1 (freeze boundary): the F1 crux
  targetProlateRemainder_unit_isTraceClassAlong
is OUTSIDE the 1055 section 5 freeze.  It speaks only about fixed-scale
(lambda = 1) model operators built in this repo from ClosedSubmodule star
projections.  It references no W_(lambda,S) quadratic form, no
lambda -> infinity asymptotics, no one-crossing readback.

RULING 2 (anti-conflation): F1 is NOT the P1 item of the 1055 revival
conditions.  1055 P1 asks for HS/trace legality of
  Pi_-(W_(lambda,S)) C_S(g) Pi_+(W_(lambda,S))
for a self-adjoint realization that does not exist in the literature.
F1 asks for trace legality of OUR concrete K_S = E Q_S E - R_S at lambda = 1.
Related names, different objects.  The day anyone cites a proof of F1 as
"funding" the revival of the prolate asymptotic family, that citation is
out of rules and must be rejected.

RULING 3 (scope verdict): F1 is GO as brick #2, but it is RECLASSIFIED.
It is neither one-line ideal-property plumbing (the shortcut fails - see
section 3) nor RH-level analysis (the source-side blueprint transfers
whole).  It is two fixed-scale estimate certificates plus one generic
reduction generalization, and every input is already in the repo or is a
table with known constants.
```

## 1. What Was to Be Decided

Brick #1 (`16b5f96`) left exactly one sorry in the mainline leaf:

```text
ConnesWeilRH/Dev/C1ProlateResponseTraceLegalityUnitScale.lean:117-121
theorem targetProlateRemainder_unit_isTraceClassAlong
    (family : FinitePrimePowerFamily) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) :
    IsTraceClassAlong basis (targetProlateRemainder unitSoninScale family) := by
  sorry
```

Two questions were on the table before spending a build on brick #2:

1. **Legality.** Does chasing F1 violate the 1055 §5 freeze on the semilocal
   prolate family (AGENTS §7d repeats the clause: "No new probe, table, or
   conditional Lean owner may reference `W_(lambda,S)` / prolate
   asymptotics...")?
2. **Nature.** Is F1 ideal-theoretic plumbing (bounded conjugation carries
   trace class, case closed) or genuine new analysis?

## 2. Legality: the boundary is clean, and it must stay written down

The frozen object (1055 §4-5) is a cross-spectral energy functional of a
self-adjoint `W_(lambda,S)` in the regime `lambda -> infinity`.  The F1
object is assembled from six concrete projections on
`cc20GlobalLogCrossingL2` (`finiteSCarrier`), each one defined as the
orthogonal projection onto a named `ClosedSubmodule`:

```text
radialSupportProjection          = starProjection (log radial window)
sourceFourierSupportProjection   = starProjection (H_inf^-1 window)
targetFourierSupportProjection   = starProjection (H_S^-1 window)
sourceSoninProjection            = starProjection (intersection)
targetSoninProjection            = starProjection (semilocal intersection)
                                   (= gramCorrectedTargetSoninProjection,
                                      proved in the repo)
targetProlateRemainder           = E Q_S E - R_S
```

Self-adjointness here is internal (`IsStarProjection`, proved by
`isStarProjection_starProjection`), not the external P0 the literature
lacks.  Positivity of `K_S` is already a sorry-free theorem
(`targetProlateHilbertSchmidtFactor_adjoint_comp_self`, brick #1 file
lines 83-107).  The scale is the literal unit:

```text
unitSoninScale = (1 : CCM24SoninScale)     -- CCM24UnitScaleProlateAlignment.lean:30
```

No limit, no asymptotics, no readback of a `W`-spectral projection.  Legal.

Ruling 2 guards the other direction.  The freeze exists because the family
had "no definable, decidable first gate" (1055 §5).  Proving our OWN model
operator trace-class at a fixed scale does not repair that gate; it must not
be bookkept as if it did.

## 3. Nature: why the plumbing shortcut fails (checked, not assumed)

The tempting shortcut was: if the finite Euler transport `T_S` were a
physical-side multiplier, it would commute with the radial projection, the
whole target configuration would be the `T_S`-image of the source
configuration, and the trace-class two-sided ideal property would close F1
in lines.  The transport definition kills this:

```text
ConnesWeilRH/Source/CC20Concrete/CCM24EulerTransport.lean:92-110
(ccm24PrimeEulerTransportEquiv p u) t = u t - c_p * u (t - log p)

ConnesWeilRH/Source/CC20Concrete/CCM24EulerTransport.lean:182-206
ccm24FiniteEulerTransportEquiv S = prod_{p in S} (1 - c_p * Shift_{-log p})
                                   : H ≃L[ℂ] H
```

`T_S` is a polynomial in TRANSLATIONS, not a multiplier.  Translations move
support windows, so `T_S` does not commute with `radialSupportProjection`,
the configuration is not a transported copy, and the ideal-property route
is closed.  The brick #1 docstring's claim ("only a bounded invertible
map... does not apply directly") is confirmed at the exact consumption
point:

```text
ConnesWeilRH/Source/CC20Concrete/ProlateTraceReduction.lean:212-217
theorem prolateFactor_summable_of_strictAngle
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (U : H ≃ₗᵢ[ℂ] H)                          <-- ISOMETRY REQUIRED HERE
    (hangle : ‖prolateFactor U‖ < 1)
    (hdefect : Summable fun i => ‖prolateDefectFactor U (basis i)‖ ^ 2) :
    Summable fun i => ‖prolateFactor U (basis i)‖ ^ 2
```

The isometry of `U` is consumed exactly where `U† = U⁻¹` identifies the
orthogonal projection of the transported subspace with the transported
projection.  `H_S = T_S H_inf T_S⁻¹` is an involution (proved:
`ccm24SemilocalHardyTitchmarsh_involutive`) but not isometric, so this is
precisely where a Gram correction must enter - and the repo already owns
the Gram bridge on the Sonin side:

```text
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSProjectionTrace.lean:141-150
targetSoninProjection_eq_gramCorrected :
  targetSoninProjection lambda family = gramCorrectedTargetSoninProjection (transportData ...)
```

## 4. What F1 actually reduces to (the brick #2 plan)

The source-side unconditional theorem is a two-premise scheme
(`CCM24UnitScaleProlateTraceReduction.lean:514-524`):

```text
premises discharged at line CCM24UnitScaleStrictAngle.lean:1501-1507:
  hangle    : ‖unitProlateFactor‖ < 1              (norm_unitProlateFactor_lt_one)
  hcrossing : Summable ‖unitRawSupportCrossing e_i‖² (additive-kernel identification)
```

F1 is the same scheme with the target's own copies of the two premises, so
brick #2 splits three ways:

```text
+-------+----------------------------------------------+--------------------+
| piece | content                                     | kind               |
+-------+----------------------------------------------+--------------------+
| 2a    | generalize prolateFactor_summable_of_...    | Lean generic       |
|       | from U : ≃ₗᵢ[ℂ] to U : (≃L[ℂ], U²=1); the   | reduction, reprove |
|       | two identities needing U†=U⁻¹ become Gram-  | the A†A algebra    |
|       | corrected identities supplied by            | with gramCorrected |
|       | CCM24SoninProjectionBridge-style machinery  | lemmas             |
+-------+----------------------------------------------+--------------------+
| 2b    | target angle bound ‖prolateFactor_S‖ < 1    | table of estimates |
|       | by perturbation from the source bound:      | from committed     |
|       | ‖T_S - 1‖ <= sum_p p^(-1/2)/(1-...) with    | constants          |
|       | norm_ccm24PrimeEulerContraction_lt_one;     | (non-RH)           |
|       | needs source margin > transport norm        |                    |
+-------+----------------------------------------------+--------------------+
| 2c    | target raw-crossing HS: translation         | decay argument     |
|       | polynomial applied to the unit-scale        | transfers with    |
|       | crossing operator keeps it HS with shifted  | explicit constants |
|       | kernel; unit-scale Gaussian/Bessel decay    |                    |
|       | survives bounded kernel shifts              |                    |
+-------+----------------------------------------------+--------------------+
```

Pre-flight check for 2b before any Lean work: pin the numerical margin of
`norm_unitProlateFactor_lt_one` against the worst `S` the visible-prime
setup allows.  If margin < transport bound at some allowed `S`, the scheme
needs a sharper angle argument and F1 is NOT free - that is the one way
this scope's GO can be revoked, and it is checkable in one paper page.

## 5. Consequences

1. F1 remains the single sorry carrier of the C1 brick thread; the brick #1
   capstone stays honestly "proven modulo F1 + two compression-HS premises".
2. The dashboard gets a new station line: `C1 brick thread: F1 scoped LEGAL,
   GO (2a/2b/2c), pre-flight margin check pending`.
3. AGENTS §7d gains the anti-conflation clause (F1 != 1055-P1) so future
   sessions cannot bookkeep F1 as a revival payment.
4. The 1055 freeze itself is untouched and still binding for
   `W_(lambda,S)`, asymptotics, one-crossing readbacks, and probes.

## 5b. AMENDMENT (same day, pre-flight fired) - see 1059

The section 4 pre-flight ran and REVOKED brick 2b as written: closing the
target angle bound by perturbing the source angle bound through the Euler
transport needs `delta > 0.985166` already at `S = {2}`
(`kappa(T_2) = (1+2^{-1/2})/(1-2^{-1/2}) = 5.828427`), while the source file
proves only `0 < unitLeakageLowerBound <= 1` qualitatively, and the visible-
prime pool `{p : 1 < p}` has no family bound so no uniform repair exists.
Full arithmetic, the surviving re-scope (2a algebra + F1 kept conditional as
R2 default, target-side angle lemma R1 by separate design record), and the
independent win (lambda(n) convention pinned from tex:967-983) are in
`docs/proofs/1059_2b_margin_revocation_and_lambda_convention_pin.md`.
Rulings 1-3 and the freeze-boundary analysis above stand untouched.

## 6. Sources

```text
ConnesWeilRH/Dev/C1ProlateResponseTraceLegalityUnitScale.lean:109-121 (F1)
ConnesWeilRH/Source/CCM20Concrete/ProlateTraceReduction.lean:212-242 (generic
  reduction; isometry at line 214)
ConnesWeilRH/Source/CC20Concrete/CCM24EulerTransport.lean:92-110, 182-206
  (transport = translation polynomial; pairwise commutation of contractions)
ConnesWeilRH/Source/CC20Concrete/CCM24SemilocalFourierSupport.lean:29-66
  (H_S = T_S H_inf T_S⁻¹; involutive)
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSProjectionTrace.lean:73-190
  (six projections; K_S factor identity; gramCorrected bridge)
ConnesWeilRH/Source/CCM25Concrete/CCM24UnitScaleProlateTraceReduction.lean:
  10-21, 498-524 (source blueprint; two-premise shape)
ConnesWeilRH/Source/CCM25Concrete/CCM24UnitScaleStrictAngle.lean:1492-1507
  (source premises discharged unconditionally)
docs/proofs/1055_semilocal_p2b_verdict.md sections 4-6 (freeze text)
the live route hazard ledger
```
