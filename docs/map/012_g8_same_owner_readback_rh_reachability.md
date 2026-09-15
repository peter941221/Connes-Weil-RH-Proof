# 012 — G8 same-owner readback: conditional RH reachability audit

**Status:** supporting technical route audit, updated 2026-09-15 (R0 formal;
actual paired leakage/source and signed source-remainder trace limits formal;
survivor/boundary mixed channels paired and limited; total metric trace limit
formal under the two diagonal energy hypotheses).
It does not alter the binding route ruling in
[003](003_b1_b5_minimal_exit_route_selection.md),
does not reopen universal B1, and does not claim RH. It answers a narrower
question: whether the existing G8 positive-trace program has a genuine,
non-circular path to the selected healthy-`CompactLog` B5 exit.

**Answer:** yes, conditionally. A detector-independent same-owner readback
theorem for the G8 cutoff family would imply `SourceRH` through already
formal theorems. No such analytic theorem is presently proved, and this
audit makes its exact input, output, and anti-circularity conditions explicit.
The route is therefore **RH-reachable, ANALYTIC-OPEN**, not a completed or
feasible RH proof program.

This is not the Arakelov transport of [011](011_arakelov_bridge_program.md).
There is no external dictionary step: the G8 target is the committed internal
quantity `C1SameOwnerWeil.qw owner.sourceTest` on the exact selected owner.

## 1. The verified logical spine

The formal pieces have the following exact roles.

| Link | Committed evidence | What it proves | Status |
| :-- | :-- | :-- | :-- |
| D1 | `C1HealthyYoshidaSpectralNegativity.lean:611` | a hypothetical right-hand off-line zero is refuted by one same-detector `qw >= 0` fact | FORMAL |
| D2 | `C1P2DefectControl.lean:644-647` | a hypothetical right-hand off-line zero supplies a healthy detector with its support and visible-prime audit data | FORMAL |
| G1 | `SelectedWeilSquare.lean:36-52` | every `CompactLogTest g` has the canonical selected owner `ofCompactLogTest g` | FORMAL |
| G2 | `C1SameOwnerWeil.lean:220-221` | `(ofCompactLogTest g).sourceTest = g` definitionally | FORMAL |
| G3 | `C1G8AdjointShearGram.lean:499-577` | each G8 source cutoff is trace-class and positive on the chosen source basis | FORMAL |
| G4 | `C1G8AdjointShearGram.lean:1016-1065` | `G8SameOwnerReadbackData` implies `0 <= qw owner.sourceTest` | FORMAL |
| G5 | `C1G8P3Contradiction.lean:28-50` | G8 readback plus healthy detector data for that *same* owner is contradictory | FORMAL |

Thus the mathematical implication to be completed is not an analogy:

```text
lower-data G8 readback theorem
  -> G8SameOwnerReadbackData (ofCompactLogTest g) ...
  -> 0 <= qw g
  -> contradict the tower's qw g < 0 for the same g
  -> SourceRH
  -> the project's Mathlib RH output.
```

The owner equality in G2 is essential. It prevents the familiar invalid move
of obtaining negativity on a Yoshida detector but positivity on a different
test, square, support interval, or finite-prime owner.

## 2. The one remaining analytic object

The G8 readback contract has only two analytic fields:

```text
remainder : Nat -> Real
remainder(n) -> 0

trace(sourceBasis, g8SourceCutoffPairData owner lambda family ... n).re
  - remainder(n)
  -> qw(owner.sourceTest).
```

Every finite-cutoff positivity and trace-class obligation is already supplied
by the concrete G8 construction. In particular, the missing theorem is not
"the limit of positive quantities is positive"; that consumer is already
formal. It is the signed same-owner identification of the particular G8
trace limit with the particular Weil value.

For the selected owner, the finite Euler family must be the existing
canonical object

```text
g8CanonicalFamily owner := FinitePrimePowerFamily.ofSelectedOwner owner.
```

`C1G8P1CanonicalFamily.lean:32-67` proves its terms and visible primes are
exactly the owner's nonzero finite prime-power terms. This removes a second
possible owner mismatch; it does not prove the required limit.

The present analytic bottleneck is already named in the G8 ledger. Records
1327--1328 of [006](006_new_math_creation_workflow.md) reduce both P1
channels to a common full-carrier antiresonant column-energy premise. Its
specialization is a Hilbert--Schmidt / asymptotic antiperiodicity statement,
not a numerical estimate. Metric-to-radial cutoff identification, the
endpoint comparison, and the P2 residual limit remain open alongside it.

## 3. The admissible producer contract

The target must not be an existential bundle of healthy-detector data and
readback data. Such a bundle would hide the desired contradiction in a
premise, which [007](007_b5_quantifier_repair_and_target_ladder.md) forbids.

Instead the program has two separately proved parts.

```text
TOWER/GEOMETRY PART
  from a hypothetical right-hand off-line zero rho,
  construct g with HealthyYoshidaDetectorData rho g
  and expose only its raw orbit-construction geometry.

G8 READBACK PART
  for every g carrying that raw geometry,
  construct parameters lambda, canonical finite-prime family, bases,
  and G8SameOwnerReadbackData (ofCompactLogTest g) lambda family ... .
```

The G8 readback part may use the construction's support, convolution,
interpolation, and finite-visible-prime information. It may not assume any
of the following:

- `HealthyYoshidaDetectorData rho g` itself;
- `0 <= qw g`, `qw g < 0`, `SourceRH`, or a spectral sign conclusion;
- an all-tests or universal Weil-positivity statement;
- an external trace-formula dictionary.

The first prohibited item matters most. The final composition is allowed to
combine raw geometry with health data, but the analytic theorem that creates
the readback must stand independently of the contradiction it will later
consume.

Record [1464](../proofs/1464_g8_r0_raw_orbit_geometry.md) completes the first
formal packaging task. The leaf
`C1G8R0OrbitGeometry.lean` defines `OrbitG8Geometry rho g` with the raw
selected-owner factorization, orbit interpolation values, centered orbit
identity, finite zero control, fourth-order tail, support interval, and
visible-prime cutoff. Its producer is proved directly from the raw-target
orbit construction plus the tail-start construction; it does not invoke the
theorem that constructs `HealthyYoshidaDetectorData`. This is the R0
compatibility export, not the missing sign theorem.

The exact producer type is packaged existentially as
`∃ g, Nonempty (OrbitG8Geometry rho g)`: the geometry is Type-valued because
it retains the orbit base, correction, and iteration index. The paired audit
reports only `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.
This closes R0 only. It does not itself instantiate the G8 cutoff trace on
that owner, prove the R2 same-owner trace identity, or supply any R3 limit.

Record [1466](../proofs/1466_r3_moving_scale_source_commutator_trace_legality.md)
now proves trace-class legality of the complete source Sonin-detector
commutator at every selected scale, along the explicitly named global basis.
It also splits that same-basis ordinary trace exactly into the outer pair and
the coupled second-support/prolate remainder. This uses the all-scale
prolate-factor square-sum but still does not identify the source commutator
with the G8 cutoff ledger or prove a vanishing remainder and same-owner `qw`
readback. R2/R3 readback therefore remains open.

Record [1467](../proofs/1467_r3_canonical_finite_euler_corner_trace.md) also
closes trace legality for the source root-completed corner at the selected
owner's exact canonical finite-prime family, and gives its ordered renewal
readback along the same named basis. This is a source-corner result; it does
not identify the corner with `g8SourceCutoffPairData` or supply the G8 cutoff
limit. The source/G8 comparison and R3 readback remain open.

Record [1479](../proofs/1479_r3_actual_cutoff_cross_trace_limit.md) proves
the uniformly bounded doubled strong limit for the actual source-compressed
physical cutoff and transfers ordinary-trace convergence for the literal
leakage/source cross channel. Record 1481 closes its adjoint orientation and
real paired trace limit. Record 1480 also proves convergence of the same-owner
signed source-remainder response through this cutoff. These results do not
establish the full G8 ledger limit, remainder decay or its identity with the
complete readback remainder, or `G8SameOwnerReadbackData`; the trace-to-`qw`
step remains open.

## 4. Milestones and stop rules

| Stage | Required delivery | Current evidence | Stop rule |
| :-- | :-- | :-- | :-- |
| R0 | Define raw `OrbitG8Geometry g` and prove that the pinned tower construction exports it without mentioning a sign conclusion | FORMAL: record 1464 packages the selected-owner factorization, raw interpolation/orbit/zero/tail data, support, and visible-prime cutoff without a health/sign field | If the only available source for a required field is a healthy/sign proposition, the producer is circular and stops |
| R1 | Instantiate the canonical owner and `g8CanonicalFamily` on the raw geometry; state all scale and basis choices explicitly | owner equality and canonical family are formal | If a cutoff construction changes `sourceTest`, square, or prime family, it is a route mismatch and stops |
| R2 | Prove a finite-cutoff same-owner trace identity with a named remainder | positive cutoff and selected-support residual decompositions are formal | An identity that reads a different response, basis, or prime support does not count |
| R3 | Prove remainder convergence and the trace-to-`qw` limit, giving `G8SameOwnerReadbackData` | PARTIAL FORMAL: records 1479 and 1481 close both actual leakage/source cross-channel orientations and their real paired limit; record 1480 closes the same-owner signed source-remainder sandwich limit; records 1482–1483 pair the survivor/boundary orientations and prove their mixed-channel limit; record 1484 identifies the two diagonal traces as actual detector-root column energies at each cutoff; record 1485 proves both that a finite real diagonal limit requires the uncut same-owner root columns to be square-summable and that this square-sum suffices for the conditional actual-cutoff limit. The square-sum estimates, diagonal limits, remainder decay/full readback identity, and endpoint/P2 limits remain open | A bound that uses a pre-assumed `qw` sign, RH, or a universal gate is circular and stops |
| R4 | Add the short formal wrapper from R0--R3 to `healthy_sourceRH_of_right_detector_specific_qw_nonneg` and audit its axioms | D1--G5 are formal | No theorem may be advertised as RH until this wrapper builds and audits green |

R0--R1 are type/owner audits. R2--R3 are the new mathematics. R4 is
composition only. This ordering forbids spending on an analytic remainder
estimate before verifying that it lands on the actual detector selected by
the tower.

## 5. Why this can reach RH, and what it does not establish

This plan can reach RH because R3 has a strictly local conclusion,
`G8SameOwnerReadbackData` for a specified owner, and the existing B5 theorem
turns that conclusion into the detector-specific contradiction. It does not
need to prove `qw >= 0` for every compactly supported test.

That logical fact is not evidence that R3 is feasible. The G8 readback
limit may still have RH-level difficulty; the named column-energy and
remainder problems are precisely where such difficulty can live. The plan
therefore supplies a correctly typed attack surface, not a probability claim
or a shortcut around the wall.

The phase/density discussion in [004](004_endpoint_literature_interface_audit.md)
section 8 continues to rule out a new universal in-category positivity
campaign. This record does not contest it. G8 is the already-selected B5
same-detector route, and its target is a lower-data trace identity for the
tower's selected geometry, not a fresh claim that density inputs prove the
universal gate.

## 6. Immediate allowed work

1. Run R0 as a source/Lean API audit: enumerate the raw construction data
   needed by G8 and prove or disprove that it can be exported without the
   healthy-sign wrapper.
2. If R0 passes, formulate R2 as one exact same-owner finite-cutoff identity
   before attempting any estimate. It must expose its remainder explicitly.
3. Price R3 only after R2 identifies the one remainder and the one analytic
   norm/endpoint estimate it needs. Do not substitute numerical evidence
   for convergence.
4. If R0 or R1 fails, record a typed owner/geometry mismatch in [006](006_new_math_creation_workflow.md)
   and return to the current freeze; do not repair it by changing the
   detector, its square, or its finite-prime family.

### R3 audit update (record 1419, 2026-09-14)

The source audit now fixes the R3 decomposition. The G8 source cutoff has a
formal four-channel trace ledger (`C1G8AdjointShearGram.lean:1297-1360`), and
the physical endpoint has a formal internal-correction/complement identity
(`C1G8AdjointShearGram.lean:845-935`). P1 and P2 separately have endpoint and
visible-residual identities, but their current limits are for
`sourceBandGramResponse` and `rootSandwichedBandResponse`/`projectionResponse`,
not for `g8SourceCutoffPairData`.

Thus R3 is refined, not completed:

```text
G8 source four-channel trace
  -> metric/radial cutoff compatibility       OPEN
  -> endpoint/readback-owner identification    OPEN
  -> vanishing remainder                      OPEN
  -> G8SameOwnerReadbackData                  OPEN
```

The exact audit is [proof record 1419](../proofs/1419_r3_same_owner_limit_audit.md).
This update is formal source evidence and does not change the conditional
RH-reachability judgment in this map. The next admissible brick is R3-COMPAT,
an operator identity or trace-norm convergence theorem independent of every
sign conclusion, `SourceRH`, and universal Weil positivity.

**Correction to the proposed shortcut:** the source Sonin carrier is not known
to be finite-dimensional. Its committed definition is a closed subspace of
the global logarithmic `L2` carrier cut out by a translated half-line and a
Hardy--Titchmarsh support condition. Therefore strong convergence of expanding
window restrictions does not by itself imply trace convergence. The required
replacement is a summable source-basis column tail / Hilbert--Schmidt estimate;
this is the same antiresonant column-energy gate already recorded in [006].

The healthy-`CompactLog` B5 consumer for every stage is unchanged:
`0 <= C1SameOwnerWeil.qw g` for the detector `g` selected against a
hypothetical off-line zero, followed by the existing `SourceRH` contradiction.

### R3-F0 start (record 1420, 2026-09-14)

The first falsifier is now stated as an operator-level obligation rather than
a generic warning. `finiteSCarrier` is definitionally the global
`cc20GlobalLogCrossingL2` carrier (`CCM24FiniteSProjectionTrace.lean:73`), and
the finite cutoff factor is a reflected-window restriction of the global root
convolution (`CompactRootHalfLinePair.lean:563-581`). Therefore the finite
Hilbert--Schmidt proof does not produce a Hilbert--Schmidt limit when the
window expands.

R3-F0 asks for a named limiting source leg and either a summable source-column
bound or a typed lower-energy orthonormal source sequence that refutes its
trace-classness. The exact target and stop rule are recorded in
[proof record 1420](../proofs/1420_r3_global_source_leg_falsifier.md). Until
F0 is discharged, a window-to-trace limit cannot be treated as ordinary
convergence. The healthy-`CompactLog` B5 consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

The first paper-level obstruction is now explicit: a nonzero compactly
supported global convolution is not compact, by translating one compact test
and its nonzero convolution output to mutually disjoint locations. Therefore
F0 can succeed only through a genuine antiresonance theorem supplied by the
Sonin source compression; the finite-window factor alone cannot supply it.
This is a structural reduction, not a closure or a no-go for the compressed
G8 owner.

The formal R3-F0 translation test in [proof record
1487](../proofs/1487_r3_actual_leakage_translated_source_test_lower_bound.md)
now gives a positive eventual lower bound for the actual unit-scale leakage
leg on right translates of its own compact source test, provided that test
detects a Laplace value. This is a lower-energy orbit on the ambient global
`L2` carrier. The current theorem does not prove that the inputs form a
normalized orthonormal sequence, so it is not yet an HS or trace-class
contradiction. It also does not transfer the orbit to the source-compressed
G8 diagonal leg. R3-F0 and the G8 readback therefore remain open.

### R3-F1 candidate (record 1421, 2026-09-14)

The first new mathematical mechanism for F0 is now isolated as a paper-level
Sonin antiresonance lemma.  With `T_b u(t) = u(t+b)`, the committed source
facts are

```text
T_b(R_lambda) subset R_lambda       for b <= 0
H T_b = T_(-b) H
S_lambda = R_lambda intersect H^(-1)(R_lambda)
```

Consequently, for `u in S_lambda` and `a > 0`,

```text
||P_S T_(-n*a) u||
  <= ||P_R T_(n*a) H u||
  -> 0.
```

The right side is the `L2` tail of `H u` above `log(lambda) + n*a`.  This
blocks the ambient translated-input escape mechanism after Sonin compression
and is independent of every detector sign, `SourceRH`, and universal Weil
positivity.  The derivation and exact source evidence are in
[proof record 1421](../proofs/1421_sonin_compressed_translation_antiresonance.md).

This is a new `R3-F1` geometric premise, not an F0 completion.  A subsequent
interface audit found that the actual G8 source leg is
`G_S^(1/2) * B_infinity * J`, with no established output projection back to
the Sonin carrier.  Therefore pointwise decay of `P_S T_(-n*a) u` cannot be
promoted directly to Hilbert--Schmidt control of the G8 leg.  The corrected
two-channel target is

```text
B_infinity J = P_S B_infinity J + (I - P_S) B_infinity J,
```

with a collective source-energy estimate for the first channel and an
independent boundary/commutator trace-ideal estimate for the leakage channel.
The correction is recorded in [proof record 1422](../proofs/1422_r3_f1_interface_correction_and_leakage_target.md).
Until both channels are controlled, `G8SameOwnerReadbackData` remains OPEN
and RH remains unclaimed.

### R3-F2 candidate (record 1423, 2026-09-14)

The leakage channel now has an exact two-level operator reduction.  With `P`
the source Sonin projection and `E` the radial-support projection, the source
geometry gives `P E = P`, hence for every ambient operator `B`,

```text
(I - P) B J = (I - E) B J + (E - P) E B J.
```

For the compactly supported global root convolution, the first term is a
finite-width radial boundary crossing and is a candidate for the existing
`CompactRootHalfLinePair` Hilbert--Schmidt owner.  The second term is the
internal prolate gap, controlled only if a square-summable estimate can be
factored through `sourceProlateRemainder`.  Details and exact stop rules are
in [proof record 1423](../proofs/1423_r3_radial_boundary_capture_and_prolate_gap.md).

This does not close F0.  It changes the next proof obligation from an
unstructured global source-leg estimate to one finite boundary identity plus
one decisive prolate-gap trace-ideal theorem.

### R3-F3 trace-legality normal form (record 1424, 2026-09-14)

The source-side reduction has now been sharpened to an iff.  The new formal
leaf
[`C1G8R3TraceLegalityNormalForm.lean`](../../ConnesWeilRH/Dev/C1G8R3TraceLegalityNormalForm.lean)
proves

```text
IsTraceClassAlong globalBasis completeThreeBranch(owner, lambda)
  <->
IsTraceClassAlong globalBasis sourceSecondSupportProlateRemainder(owner, lambda).
```

The forward direction subtracts the already formal compact-root outer pair;
the reverse direction is the existing outer-pair-plus-remainder theorem.
The paired audit is green in [proof record 1424](../proofs/1424_r3_trace_legality_normal_form.md)
with zero `error:`, zero `sorryAx`, and only the three standard axioms.

This is a real R3 reduction, but its scope is exact: it closes trace legality
for the formal source three-branch ledger, not the G8 cutoff-to-`qw` limit.
The decisive remainder is therefore an exact iff obstruction, while the
G8 cutoff/source-ledger transport and the signed trace readback remain open.
No sign, detector health, `SourceRH`, or universal Weil positivity is used.

### R3-F4 scale-defect normal form (record 1425, 2026-09-14)

The next scale-reduction idea has now been made exact. Let `T_b` be global
logarithmic translation, `H` the Hardy--Titchmarsh isometry, and `P_+` the
fixed positive-half-line projection. Define the two defects

```text
D^R_b = T_b H - H T_(-b)
D^L_b = H* T_(-b) - T_b H*
```

For `b = log(lambda)`, the new formal leaf proves

```text
Q_lambda - T_b Q_1 T_(-b)
  = D^L_b P_+ T_b H + T_b H* P_+ D^R_b,
```

where `Q_lambda` is the actual source Fourier-support projection. Hence the
unit-scale reduction is valid exactly when the two defects vanish (or when
their displayed terms admit a suitable trace-ideal bound). The paired audit
is green in [proof record 1425](../proofs/1425_r3_hardy_translation_defect.md)
with the three standard axioms and no `sorryAx`.

This is not yet a proof of the zero-defect equation. The committed L1 Fourier
integral API contains translation covariance, but the Hardy operator acts on
the global L2 carrier; the L2 extension is the next new-mathematics target.
Even after zero defect, transport of the Sonin intersection projection and
the G8 cutoff-to-source readback remain open. R3 and RH are not claimed.

### R3-F5 zero-defect closure (record 1427, 2026-09-14)

The anticipated L2 extension is now connected to the R3 defects. The new
formal leaf
[`C1G8R3ZeroDefectClosure.lean`](../../ConnesWeilRH/Dev/C1G8R3ZeroDefectClosure.lean)
imports the already landed global L2 Hardy translation theorem and its
self-adjointness theorem, and proves for every `b`:

```text
hardyTranslationRightDefect b = 0
hardyTranslationLeftDefect b = 0
```

The exact F4 decomposition therefore yields

```text
sourceFourierSupportProjection lambda
  = logTranslation (log lambda)
      * sourceFourierSupportProjection unitSoninScale
      * logTranslation (-log lambda).
```

Here `*` denotes composition in the displayed operator identity. The paired
audit is green in [proof record 1427](../proofs/1427_r3_zero_defect_scale_transport.md)
with zero `error:` lines, zero `sorryAx`, and three standard axiom prints.
This closes the exact scale-defect branch only; it does not prove any trace
limit or Weil sign.

The R3 bottleneck is consequently not Hardy covariance. It is still the
cutoff/source-ledger compatibility and the summable source second-support
prolate remainder (including the Sonin leakage channel) identified in F3 and
F2. The healthy-`CompactLog` B5 consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

### R3-F6 doubled-shift Hardy involution (record 1428, 2026-09-14)

The opposite scale motion of the radial and Fourier projections leaves a
relative displacement of twice the logarithmic scale. The new formal leaf
[`C1G8R3DoubledShiftNormalForm.lean`](../../ConnesWeilRH/Dev/C1G8R3DoubledShiftNormalForm.lean)
defines

```text
K_b = T_(2*b) H
```

on the committed `finiteSCarrier`, where `T` is global logarithmic
translation and `H` is the global Hardy--Titchmarsh operator, and proves

```text
K_b * K_b = id
```

for every real `b`. This is a formal algebraic normal form, using the already
formal Hardy translation reversal, Hardy involutivity, and translation
composition. The paired audit is green in [proof record 1428](../proofs/1428_r3_doubled_shift_hardy_involution.md)
with zero `error:` lines, zero `sorryAx`, and only the three standard axioms.

This does not close R3. It removes no trace-class or summability obligation:
the cutoff/source-ledger compatibility, the source second-support prolate
remainder, the Sonin leakage estimate, and the signed same-owner readback are
still open. The operator `K_b` is a new organizing object for those estimates,
not a positivity theorem and not an RH proof. The B5 consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

### R3-F7 finite endpoint ledger (record 1433, 2026-09-14)

The doubled-shift alternating product now has a formal finite-stage endpoint
ledger in
[`C1G8R3WeightedFiniteStage.lean`](../../ConnesWeilRH/Dev/C1G8R3WeightedFiniteStage.lean):

```text
v in the doubled-shift Sonin intersection -> T_b v = v
                                      -> T_b^n v = v for every n
||T|| <= 1 -> ||weightedCommutatorStage T D n||
             <= n * ||[T,D]||
```

This is a lower-data reduction, not the missing endpoint theorem. It
identifies the spectral value `1` exactly and bounds the algebraic finite
stage, but supplies no summable detector-weighted tail. R3 remains open at
the trace-norm limit and same-owner readback; RH is not claimed.

### R3-F8 strong-to-HS endpoint transfer (record 1434, 2026-09-14)

The new formal lemma
[`C1G8R3WeightedStrongToHS.lean`](../../ConnesWeilRH/Dev/C1G8R3WeightedStrongToHS.lean)
proves that strong convergence on every detector-root column, together with
uniform contraction bounds and one Hilbert--Schmidt square-sum, forces the
weighted square energy to converge to zero.  This removes one false choice:
R3 does not need operator-norm convergence if the detector root supplies the
Hilbert--Schmidt weight. Record 1436 also discharges the second-sided fixing
identity of the intersection projection. The missing strong-limit theorem is
the classical no-gap alternating-projection theorem on the actual carrier:
prove strong convergence of `(p_b q p_b)^n` to the intersection projection.
It is open as a Lean/formalization and source-API task, not a license to
assume a spectral gap. The transfer lemma itself is lower-data only; R3 and RH
remain open.

### R3-F9 conditional HS-pair trace transfer (record 1476, 2026-09-15)

The new generic theorem
[`tendsto_ordinaryTraceAlong_pairSandwich_of_strong`](../../ConnesWeilRH/Dev/C1G8R3StrongTracePairTransfer.lean)
proves trace convergence for a fixed Hilbert--Schmidt pair under a uniformly
bounded, pointwise-convergent doubled cutoff. Its summable diagonal majorant
comes from the two fixed adjoint HS column sequences. The theorem is also
instantiated on the existing three-branch `sourceBandGramResponse` owner, so
the P1 source-band trace can use this conditional continuity step. See
[proof record 1476](../proofs/1476_r3_strong_pair_sandwich_trace_transfer.md).

This does not instantiate the hypotheses on the literal G8 window sequence:
that factor varies with the window and surrounds `g8AdjointShearGram` on the
ambient carrier, rather than sandwiching a fixed P1 HS pair on the source
carrier. Records 1479 and 1480 now cover the actual cutoff for the
leakage/source cross channel and the same-owner signed source-remainder
response. The other G8 metric channels, remainder decay/full readback identity,
`G8SameOwnerReadbackData`, the detector-specific semi-local sign, C3, and RH
remain open. This is a formal conditional trace lemma, not a change to the
route status.

### R3-F10 expanding output-window strong limit (record 1477, 2026-09-15)

The symmetric output-interval projections now formally converge strongly to
the identity on the global logarithmic L2 carrier. The proof identifies each
projection with its AE interval indicator and sends the squared tail integral
to zero by monotone convergence; the paired audit prints only the three
standard axioms. See
[proof record 1477](../proofs/1477_r3_expanding_output_projection_strong_limit.md)
and supporting route record
[032](032_r3_expanding_output_projection_strong_limit.md).

Record 1478 now composes the projection limit with the fixed global
convolution and source inclusion, proving strong convergence of the actual
physical factor and its adjoint, including the source compression and its
adjoint. Record 1479 supplies the source-compression uniform bound and doubled
strong convergence, then proves ordinary-trace convergence for the literal
leakage/source cross channel using the fixed source three-branch HS pair.
Record 1481 proves the reverse source/leakage channel is the adjoint of the
forward channel and closes their real paired trace limit. Record 1480
separately transfers the same cutoff through the fixed same-owner first-jet
and source three-branch pairs, proving ordinary-trace convergence of their
signed source remainder. Neither theorem proves that this remainder limit is
zero or identifies it with the complete G8 readback remainder. The three
other coframe channels, same-owner `qw` readback, detector semi-local sign,
C3, and RH remain open.

### R3-F11 physical cutoff factor strong limit (record 1478, 2026-09-15)

The actual support-owned finite factor is now identified exactly as the
reflected physical output projection composed with the fixed global detector
convolution. Its projection tails vanish in L2, yielding pointwise strong
limits for the factor and its adjoint. The same result passes through the
actual Sonin inclusion on both sides, including the adjoint compression. This
is formal operator compatibility for the literal G8 owner. Record 1479 adds a
uniform doubled bound and trace limit for the leakage/source channel, and
record 1481 closes its adjoint orientation and real paired limit. The full G8
readback still requires the three other coframe channels and signed remainder
identification. See
[proof record 1478](../proofs/1478_r3_physical_cutoff_factor_strong_limit.md)
and supporting route record
[033](033_r3_physical_cutoff_factor_strong_limit.md). Records 1479/1481 close
the actual cross-channel pair; they do not read the full ledger back as `qw`.
The healthy-`CompactLog` B5 consumer and binding route are unchanged.

### R3-F12 actual cutoff cross-channel trace limit (record 1479, 2026-09-15)

The physical source compression is uniformly bounded by the fixed global
detector-convolution norm. Combined with the factor and adjoint strong limits
from record 1478, the new general doubled-product lemma proves strong
convergence of `C_n * C_n†`. The literal finite-window leakage/source channel
is exactly `C_n† * (-sourceBandGramResponse†) * C_n`. The fixed source
three-branch Hilbert--Schmidt pair from the existing source trace ledger and
the transfer theorem from record 1476 therefore give its ordinary-trace limit.
The limit remains the same-detector source response between two compressed
global convolutions. Record 1481 closes the reverse orientation by adjoint
symmetry and gives the real paired cross-channel limit. Record 1480 proves
convergence of the same-owner signed source-remainder sandwich through this
cutoff. The three other survivor/boundary coframe channels, remainder
decay/readback, and trace-to-`qw` identification remain open. See
[proof record 1479](../proofs/1479_r3_actual_cutoff_cross_trace_limit.md) and
[supporting record 034](034_r3_actual_cutoff_cross_trace_limit.md).

### R3-F13 survivor/boundary mixed-channel pairing and limit (records 1482–1483, 2026-09-15)

The survivor/boundary and boundary/survivor channels of the separate G8 metric
four-channel ledger are formal adjoints at every literal cutoff. Their
ordinary traces therefore combine into one real sequence, exactly twice the
real part of either ordered trace. Record 1483 proves the ordinary-trace limit
of one orientation through the actual cutoff, with limit the same-owner
compressed source response, and a Lean theorem assembles both orientations
into the corresponding real paired limit. This closes the mixed-channel
limit only. It does not provide prime-power
readback or sign. The survivor-survivor and boundary-boundary limits, total
four-channel limit, signed remainder/full-readback identity, and
`G8SameOwnerReadbackData` remain open. See [proof records
1482](../proofs/1482_r3_actual_cutoff_survivor_boundary_pair.md) and
[1483](../proofs/1483_r3_actual_cutoff_survivor_boundary_trace_limit.md), and
[supporting map records 037](037_r3_actual_cutoff_survivor_boundary_pair.md)
and [038](038_r3_actual_cutoff_survivor_boundary_trace_limit.md).

### R3-F14 diagonal detector-root energy normal form (record 1484, 2026-09-15)

For either diagonal metric coframe `L`, the literal cutoff channel is formally
`A_n† A_n`, where `A_n` is the selected convolution root after `L` and the
actual source compression. Its ordinary trace is exactly the squared column
sum on the named source basis. This makes the missing diagonal limit an
explicit same-basis detector-root energy problem. Each finite-cutoff sum is
finite, but no uniform domination or convergence in `n` follows. The leakage
and common-right detector-root square-sum gates remain open, as do full G8
readback and R3. See [proof record
1484](../proofs/1484_r3_actual_cutoff_diagonal_root_energy.md),
[supporting map record 039](039_r3_actual_cutoff_diagonal_root_energy.md),
and route records [018](018_r3_unit_detector_root_square_sum.md),
[022](022_r3_common_right_causal_telescope.md), and
[028](028_r3_moving_scale_detector_root_range_energy.md).

### R3-F15 diagonal trace-limit energy constraint (record 1485, 2026-09-15)

The actual-cutoff selected detector-root columns converge pointwise to the
uncut same-owner columns. A finite real limit forces those columns to be
square-summable by the finite-cutoff energy identities and finite-partial-sum
bounds. Conversely, that same-basis square-summability gives the actual
cutoff trace limit by the fixed-HS-pair strong-sandwich theorem. The estimate
is still open, so neither diagonal limit has been established unconditionally.
The full G8 readback, signed remainder decay, endpoint/P2 signs, and same-owner
`qw` identification remain open. See [proof record
1485](../proofs/1485_r3_diagonal_trace_limit_energy_constraint.md) and
[supporting map record 040](040_r3_diagonal_trace_limit_energy_constraint.md).

### R3-F16 conditional total metric trace limit (record 1486, 2026-09-16)

Record 1486 assembles all four channels of the literal physical G8 metric
cutoff. The survivor/boundary mixed pair has its formal limit; each positive
diagonal channel has a formal limit under its same-basis root-column
square-summability hypothesis. Therefore both diagonal energy hypotheses
together imply convergence of the complete four-channel metric trace to the
sum of the two uncut root-energy traces and the mixed-pair limit. This is not
an unconditional estimate and does not identify the limit with `qw`; the
signed endpoint remainder, its vanishing, the full readback identity, and
endpoint/P2 signs remain open. See [proof record
1486](../proofs/1486_r3_total_metric_cutoff_trace_limit.md) and
[supporting map record 041](041_r3_total_metric_cutoff_trace_limit.md).

### R3-F17 ambient leakage energy obstruction (records 1488–1489, 2026-09-16)

The actual unit-scale leakage leg has a normalized orthonormal input sequence
in the ambient `finiteSCarrier` on which its squared output norms are not
summable. This is formal evidence against seeking a Hilbert--Schmidt bound for
the uncompressed ambient leg. It does not supply a counterexample to the G8
diagonal energy claims: those use root-leg columns after the literal source
compression and sum over a basis of `sourceSoninCarrier`. The transfer from
the ambient orbit to that compressed same-basis sum is still missing, as are
both diagonal energy estimates and the full trace-to-`qw` readback. See
[1488](../proofs/1488_r3_leakage_orthonormal_translation_orbit.md),
[1489](../proofs/1489_r3_leakage_orthonormal_orbit_energy_obstruction.md), and
[supporting map record 018](018_r3_unit_detector_root_square_sum.md).
