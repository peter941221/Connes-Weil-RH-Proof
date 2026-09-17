# 012 — G8 same-owner readback: conditional RH reachability audit

**Status:** supporting technical route audit, updated 2026-09-16 (R0 formal;
actual paired leakage/source and signed source-remainder trace limits formal;
survivor/boundary mixed channels paired and limited; total metric trace limit
formal under the two diagonal energy hypotheses; radial-boundary finite-window
support, translation, and source-basis energy formal; internal-gap and full
source-Sonin leakage same-basis energy formal; diagonal leg operator-bridge
audit registered as map 042, splitting both diagonal obligations into
in-Sonin and leakage-band families on the source carrier).
It does not alter the binding route ruling in
[003](003_b1_b5_minimal_exit_route_selection.md),
does not reopen universal B1, and does not claim RH. It answers a narrower
question: whether the existing G8 positive-trace program has a genuine,
non-circular path to the selected healthy-`CompactLog` B5 exit.

**Bookkeeping correction (2026-09-16):** the previously listed S3, B3/B4,
`rho5`, and C3 are not four independent gates. S3 and B3/B4 are the two
currently open components of one total diagonal-energy package (possibly
proved by one stronger Hilbert--Schmidt theorem); `rho5` is the separate
same-object arithmetic bridge. C3, namely `qw >= 0`, is already the formal
consumer of `G8SameOwnerReadbackData` and is not an additional producer goal.

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

### R3-F2 radial-boundary/internal-gap split (records 1423 and 1494)

The leakage channel has an exact two-level operator reduction, now formal in
Lean for the selected root convolution and actual source inclusion (proof
record 1494). With `P`
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

The cancellation identity alone does not estimate either term in the relevant
trace ideal, so it does not close F0. Record 1495 now formally identifies the
zero-boundary crossing with the finite compact-output factor and transports
that factor to the actual radial cutoff on the same source inclusion. The
source-basis boundary estimate and the decisive prolate-gap trace-ideal
theorem remain open. See [proof records
1423](../proofs/1423_r3_radial_boundary_capture_and_prolate_gap.md),
[1494](../proofs/1494_r3_radial_boundary_internal_gap_split.md), and
[1495](../proofs/1495_r3_radial_boundary_finite_window_identity.md).

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

### R3-F18 source projection of the ambient orbit vanishes (record 1490, 2026-09-16)

The direct candidate transfer, projecting the R3-F17 ambient orbit into the
unit-scale `sourceSoninCarrier` and then renormalizing, is now ruled out by a
formal norm limit. The source Fourier-support projection of those separated
right translates tends to zero by the Hardy translated-tail theorem; the
complete Sonin projection factors through that Fourier-support projection
and is contractive. Thus the projected vectors tend to zero as well. This is
not a counterexample to the actual G8 energy estimates: those columns first
pass through the same-owner compressed convolution/coframe. A valid witness
must be constructed through that interface. See
[proof record 1490](../proofs/1490_g8_source_projection_translated_orbit_decay.md).

### R3-F19 source-prolate boundary pullback is zero (record 1491, 2026-09-16)

The pre-existing G8 visible-boundary energy lemma uses the operator
`sourceInclusion† * sourceProlateFactor * sourceInclusion` as its input. Record
1491 proves that this pullback, and hence its visible-boundary coframe image,
is identically zero: the prolate factor acts on the quotient band, while the
source inclusion lies in the orthogonal source-Sonin subspace. Thus that
summability result is valid but vacuous as evidence for the actual
same-basis `hBoundary` condition. It does not refute `hBoundary`; a nonzero
root/coframe estimate is still open. See
[proof record 1491](../proofs/1491_g8_source_prolate_pullback_zero.md).

### R3-F20 finite visible-prime boundary-energy reduction (record 1492, 2026-09-16)

The actual aggregate `hBoundary` is the selected root convolution applied to
the exact finite Schur--polar sum of visible-prime boundary outputs. Lean now
proves that if each rooted output has square-summable columns on the same
source basis, then their finite sum satisfies `hBoundary`. This isolates the
remaining producer work to the individual rooted boundary outputs; it does
not estimate any of them. See
[proof record 1492](../proofs/1492_g8_boundary_energy_finite_output_reduction.md).

### R3-F21 per-output boundary energies wired into the trace consumer (record 1493, 2026-09-16)

The per-output sufficient condition now feeds the actual four-channel G8
physical metric trace-limit theorem. The survivor diagonal energy remains a
premise, while the mixed survivor/boundary limit stays formal. Individual
rooted boundary-output estimates, the unconditional trace limit, signed
readback, and detector-specific positivity remain open. See
[proof record 1493](../proofs/1493_g8_boundary_output_trace_consumer.md).

### R3-F22 radial-boundary finite-window support and transport (record 1495, 2026-09-16)

Lean now proves that the selected root's positive-to-negative crossing at
zero is exactly the zero extension of its compact-output factor on the finite
window determined by the selected test's support. It also proves that the
actual radial source leakage is this same window operator translated to
`log(lambda)`, composed with the actual source inclusion. This closes the
support/transport identity in record 1423; it does not give a source-basis
Hilbert--Schmidt bound for the window factor or an estimate for the internal
prolate gap. The G8 diagonal energies, trace/readback, detector-specific
positivity, C3, and RH remain open. See [proof record
1495](../proofs/1495_r3_radial_boundary_finite_window_identity.md) and [map
record 018](018_r3_unit_detector_root_square_sum.md).

### R3-F23 radial-boundary source-basis energy (record 1496, 2026-09-16)

The compact-output kernel's basis square-sum now passes through the actual
source inclusion and radial translation. Lean proves that the selected-root
radial-boundary outputs are square-summable on any named `sourceSoninCarrier`
basis. This closes the radial-boundary summand in the leakage split as one
Hilbert--Schmidt factor. The internal prolate gap is closed by record 1497;
the separate G8 visible-prime boundary-output energies remain open, and the
result does not by itself give a G8 trace-to-`qw` limit. See [proof record
1496](../proofs/1496_r3_radial_boundary_source_energy.md), [1423](../proofs/1423_r3_radial_boundary_capture_and_prolate_gap.md),
and [map record 018](018_r3_unit_detector_root_square_sum.md).

### R3-F24 internal prolate-gap source-basis energy (record 1497, 2026-09-16)

The internal radial-but-non-Sonin gap is now square-summable on any named
source basis. The proof combines the all-scale prolate-factor adjoint with the
reflected compact-root crossing, yielding an exact two-term decomposition of
the selected-root source-band leg. Together with record 1496 and the exact
record-1494 split, Lean now proves the complete selected-root source-Sonin
leakage is square-summable on any named source basis. The separate
finite visible-prime G8 boundary-output energies, actual diagonal energies,
and same-owner trace-to-`qw` readback remain open; detector-specific
semi-local positivity, C3, and RH are not claimed. See [proof record
1497](../proofs/1497_r3_internal_prolate_gap_source_energy.md) and
[supporting map record 018](018_r3_unit_detector_root_square_sum.md).

### R3-F25 diagonal leg operator-bridge audit (map 042, 2026-09-16)

A source-level audit (zero new Lean) fixes what record 1497 does and does
not supply for the two diagonal energy hypotheses `hSurvivor`/`hBoundary`
consumed by records 1485/1486/1493. Quoted from committed definitions:
every actual G8 metric coframe factors as
`ambient ∘L sourceInclusion λ ∘L sourceSide` (the survivor coframe has
ambient factor `I` because the empty Euler product is the identity), while
record 1497's object is `(I − P) ∘L C ∘L J`. The two obligations are
therefore NOT supplied: the left projection removes the in-Sonin (signal)
half of the norm, the input maps differ, and the boundary legs insert an
ambient factor between root and inclusion. The bridge converts both
obligations into source-carrier normal forms: the survivor energy reduces
exactly to the in-Sonin square-sum `Σ‖J† C J s_S e_i‖²` (its out-of-Sonin
half is a free corollary of 1497 via bounded right precomposition), and
each boundary output `M_p ∘L J ∘L N_p` splits into an in-Sonin family
`J† C M_p J N_p` plus the record-1494 leakage legs `(I−E) C M_p J` and
`(E−P) E C M_p J`, which need `M_p`-adapted versions of the record
1495/1496 window identity and the record 1497 prolate absorption. Work
orders WO-S (S1–S3) and WO-B (B1–B4), with stop rules and the ambient
shortcut blocks (records 1488–1491), are registered in
[map 042](042_g8_diagonal_leg_operator_bridge_audit.md). No estimate is
proved; R3, the trace-to-`qw` readback, and RH remain open.

### R3-F26 survivor coframe source bridge, WO-S S1+S2 landed (record 1498, 2026-09-16)

[`C1G8R3SurvivorCoframeBridge.lean`](../../ConnesWeilRH/Dev/C1G8R3SurvivorCoframeBridge.lean)
lands bricks S1 and S2 as exact operator identities: the survivor coframe is
`u • (J ∘L s_S)` with `s_S` purely source-side, and on the ambient carrier
`‖v‖² = ‖J† v‖² + ‖(I − P) v‖²` holds by Pythagoras at the projection
`P = J J†` alone (no operator-norm input). Consequences: the OUT leg is free
by record 1497 plus bounded right precomposition, and the survivor energy is
UNCONDITIONALLY equivalent to the single in-Sonin square-sum
`Σ‖J† C J (s_S e_i)‖²` on any named source basis. S3 (that square-sum) is
now the sole survivor obligation and stays open. See [proof record
1498](../proofs/1498_r3_survivor_coframe_source_bridge.md).

### R3-F27 boundary output factorization bridge, WO-B B1+B2 landed (record 1499, 2026-09-16)

[`C1G8R3BoundaryOutputFactorizationBridge.lean`](../../ConnesWeilRH/Dev/C1G8R3BoundaryOutputFactorizationBridge.lean)
lands bricks B1 and B2: by structural induction over the visible-prime
suffix, every actual boundary output of `suffixEulerBoundaryOutputMaps` —
hence every summand of `finiteEulerMetricCoframeBoundaryMaps` — factors
exactly as `M_p ∘L J ∘L N_p`, and each composed diagonal energy splits
exactly into the in-Sonin leg plus the record-1494 radial-boundary and
internal-gap legs with `M_p` inside. Sufficiency recombines the legs, so
per-output three-leg square-summability feeds the record-1492 consumer
unchanged. B3/B4 (`M_p`-adapted estimates) remain open — the committed
1495/1496/1497 windows are owner-root only. See [proof record
1499](../proofs/1499_r3_boundary_output_factorization_bridge.md).

### R2 full readback identity preregistered (record 1500, 2026-09-16)

The one readback identity is now pinned in a single statement: at every
cutoff stage `n` the actual total trace splits exactly (four-channel ledger)
as `t_n = b_n + 2·x_n + l_n`; `x_n → X` and `l_n → L` are FORMAL (records
1479/1480/1481), `b_n → B` is OPEN (ρ4), and the readback contract holds iff
`B + 2·X + L = qw(owner.sourceTest)` (ρ5). The substantive gate is ρ5 — the
same-owner signed value identification, i.e. the Euler/prime-power readback
— not the existence of the remainders' limits. The work-order energies
(WO-S/WO-B) route into the endpoint channel only through the committed
metric-split identity at `C1G8AdjointShearGram.lean:845-935`; any estimate
that does not land there is attached to the wrong endpoint. See [proof
record 1500](../proofs/1500_r2_full_readback_identity.md).

### R4 packaging pre-audit checklist (record 1501, 2026-09-16)

Before any R4 attempt, the composition chain (D1/D2 → G1–G5 → R0, with file
and line citations), the five anti-circularity audits (statement purity,
same-owner pinning, proof-input allowlist, parameter hygiene, composition
minimality), and the final-claims audit (axiom print, Mathlib RH statement
verbatim, "RH-reachable, ANALYTIC-OPEN" until the wrapper is green) are
registered as a blocking checklist. Both ρ4 and ρ5 of record 1500 must be
discharged before the audits can run on a real producer. See [proof record
1501](../proofs/1501_r4_packaging_audit_checklist.md).

### R2 ρ4 endpoint channel limit discharged conditionally (record 1502, 2026-09-16)

[`C1G8R3ActualEndpointTraceLimit.lean`](../../ConnesWeilRH/Dev/C1G8R3ActualEndpointTraceLimit.lean)
identifies the readback trace as the endpoint channel operator
`J† ∘L Wₙ† ∘L G ∘L Wₙ ∘L J` (fixed adjoint-shear Gram `G`, moving expanding
window `Wₙ`) and proves `t_n → B := tr(J† ∘L C† ∘L G ∘L C ∘L J)` by
source-basis dominated diagonal convergence, using the record-1478 strong
limit and the window factorization `Wₙ = (norm-one projection) ∘L C` for
the domination. The summable majorant is exactly the gate
`Summable ‖C(J e_i)‖²`, which is UNCONDITIONALLY equivalent to the in-Sonin
survivor core `Summable ‖(J† C J)(e_i)‖²` (exact Sonin split + record 1497
leakage): **one square-sum now gates both the survivor energy and the
endpoint limit**. ρ4 is FORMAL GIVEN the gate; the gate itself is open. See
[proof record 1502](../proofs/1502_r3_actual_endpoint_trace_limit.md).

### R3 gate attack wave preregistered; carrier geometry typed (record 1503, 2026-09-16)

The Sonin carrier is committed to be
`radial-support ⊓ comap(HT) radial-support` — a two-sided (time-band)
limiting configuration of infinite measure, so no finite-window collapse is
available. New structural findings: (i) the gate is exactly "P C P is
Hilbert–Schmidt on the ambient"; (ii) HT-conjugation never turns C into a
window (reflection-plus-multiplier sandwiches keep convolutions
convolutions), so no conjugation formality exists; (iii) **Hardy-pressure
finding** — at the classical (phase-free) limit the two-sided condition is
the Hardy-uniqueness regime, so the entire nontriviality of the carrier and
of the gate is carried by the scattering multiplier phase: any proof of the
gate must read the phase of `m`, the mechanism behind law F21. Attack
routes preregistered: W (compressed window-strip HS, formalizable), T
(aggregate tail decay through the multiplier phase; open mathematics), AO
(almost-orthogonality with phase-derived constants); B3 composite window
(log-shift unions stay compact — 1495 mechanism applies, transfer
unchanged), B4 prolate absorption with `M_p` ambient-side (1491 guard);
ρ5 one-theorem statement + P2 sub-limit split with the record-1501 A1
circularity guard. See [proof record
1503](../proofs/1503_r3_gate_attack_wave_prereg.md).

### ρ4 landed; the gate is now a named iff theorem (records 1504/1505, 2026-09-16)

ρ4 is FORMAL GIVEN (★) as a green Lean brick
(`C1G8R3ActualEndpointTraceLimit`, 11 decls): the literal readback trace
`t_n` converges to the named aggregate limit
`ordinaryTraceAlong sourceBasis (J† ∘L C† ∘L G ∘L C ∘L J)` under the
survivor core square-sum, via engine-level dominated diagonal convergence
(record-1478 strong limit + window factorization for domination; the
record-1476 transfer does not apply — cutoff sits inside, per F24 slot
analysis). Record 1504 then turns the substantive gate into ONE
machine-checked equivalence (`C1G8R3SameOwnerGateNormalForm`, 5 decls):
given (★), the zero-remainder readback holds iff `B.re = qw` — forward
direction (necessity) works for ANY readback data with arbitrary
remainder; backward direction CONSTRUCTS the zero-remainder
`G8SameOwnerReadbackData` from the single real equation, feeding the
committed positive-trace consumer unchanged. No `qw` sign anywhere in any
premise (record-1501 guard satisfied). ρ5 is thereby reduced to the
Euler-content identification of `B` — the P2 sub-limit program. Record 1505
lands Route W's abstract core (`C1G8R3RouteWWindowTailNormalForm`, 2
decls): the window/tail decomposition normal form — the gate for `T`
follows from a free window-strip square-sum plus the SAME gate for the
tail composition, and the form iterates; the tail gate is the minimal
irreducible remainder, still phase-typed per the Hardy-pressure finding.
See [1504](../proofs/1504_r5_same_owner_gate_normal_form.md) and
[1505](../proofs/1505_route_w_window_tail_normal_form.md).

### Stage-2 modulation verdict, B4 chain wired, channel cycles landed (records 1572-1574, 2026-09-17)

Record [1572](../proofs/1572_T1_exponent_ledger_stage2.md) adjudicates the
stage-2 (★)-tail question against the committed definitions: the modulation
`E` is a SHARP half-line indicator (no window symbol to decay), `Q = H E H`
makes the (★) tail and the B4 obligation ONE operator family, and the
symbol-decay reading of the modulation is typed dead (edge contributions at
most `1/log|xi|` by T0a - a logarithmic gain can never cross the power
threshold `beta > 1`). Surviving mechanisms: positive-ray stationary phase,
prolate absorption, the `hM` identity, Cotlar T2. Record
[1573](../proofs/1573_T_B4_instantiation_chain.md) wires the instantiated
1536 consumer chain for the ACTUAL boundary columns slot by slot (five named
theorems with line numbers), reducing B4 to exactly one square-sum
`B4_actual(M, D, N)` PLUS one identity question `Q-hM`; no implicit
instantiation remains, and B4's shared fate with (★) is now structural.
Record [1574](../proofs/1574_rho5_channel_cycles_and_qhm_recon.md) lands the
formal companion leaf `C1G8R5LeakageChannelCycles` (+Audit, try11 GREEN 3957
jobs, standard axioms): all three named leakage channels of record 1569
cycle from the source basis onto the BOUNDARY carriers (response onto the
actual-band pair carrier, total onto the common boundary carrier with its
minus carried as an operator `Neg`, remainder as the pair sum), giving the
ρ5 producer its OUT-side interface at the map-042 carrier split. Same
record delivers the Q-hM verdict: the Sonin carrier is radial by committed
definition, the Euler transport is a support-preserving DELAY but the actual
`M_p` contains its adjoint = an ADVANCE by `log p` per prime factor, so the
FIXED-scale `hM` shortcut is blocked for the actual columns (paper mechanism
note, not a formal no-go); B4 keeps both 1534 premises unless the registered
scale-adapted `hM'` (finite `lambda`-shift, permitted by the consumer's
quantifier) is formalized. No estimate moved anywhere; (★), B4, ρ5,
transport, R4 all OPEN. RH not claimed.

### P2 connector landed; phase wave entry fee paid (records 1569-1571, 2026-09-17)

The named follow-up of record 1567 executed: `C1G8R5LeakageChannelPSplit`
+Audit (try4 GREEN 3956 jobs, standard axioms) pins the three channels of the
1480 leakage limit operator, proves all three trace-class along the source
basis via `boundedSandwich` transports of the committed pair owners, and
restates the proven limit as the difference of the NAMED remainder-channel
and response-channel traces. The `finitePrimeSum` content of the pinned ρ5
target must therefore attach through the named remainder channel trace (or a
combination of the two), never rowwise alone. No estimate, no sign premise
(see [1569](../proofs/1569_p2_connector_leakage_channel_split.md)).

In parallel the phase wave consumed its pre-registered entry fee: record
[1570](../proofs/1570_T0_digamma_quantitative_asymptotics.md) delivers T0a/T0b
with explicit constants (`|theta' + 2*pi*log|xi|| <= 0.1138/xi^2`,
`|theta'' + 2*pi/xi| <= 0.3067/|xi|^3` for `|xi| >= 2`, DLMF-cited with the
complex sec-factor paid, corrected sign against 1568, exact-Fraction sentinel
8/8 PASS), and record [1571](../proofs/1571_T1_exponent_ledger_stage1.md)
opens the T1 exponent ledger: the two classical levers price the positive
off-diagonal ray at `beta = 5/2 > 1` but pin `beta = 1/2 < 1` on the negative
ray for ANY symbol decay, reducing the whole (★)-tail question to the
projection-modulation third source (stage 2; verdict OPEN). RH not claimed.

### ρ5 target pinned as one theorem (record 1567, 2026-09-17)

The preregistered one-theorem statement landed (`C1G8R5EulerContentBridgeTarget`
+Audit, try3 GREEN 3972 jobs, standard axioms): the gate is now the named
`Prop` `g8R5EulerContentBridge`, right side expanded through the committed
`pole - arch - prime` components, left side expanded through the four
channels, and the canonical-family arithmetic row transported to
`finitePrimeSum owner.sourceTest.convolutionSquare`.  The pinned ledger
precludes row-by-row vanishing allocations (the prime sum appears with both
signs inside the ambient ledger), so the open producer obligation is one
combined-rows identity plus the source/ambient transport; see
[1567](../proofs/1567_rho5_one_theorem_statement_and_prime_row_transport.md).
No estimate, no sign premise, no RH conclusion.

### ρ5 Euler bridge isolated (record 1507, 2026-09-16)

The formal gate now builds cleanly, but the Euler identification remains a
genuine object-level problem. The available arithmetic ledger identifies the
ordinary trace of the separate arithmetic operator with the finite visible
prime-power sum. The G8 endpoint aggregate is instead the source trace of
`J† C† G C J`; the existing source-compression identity for `G` cannot be
applied to the ambient vectors `C (J u)`. Record [1507](../proofs/1507_r5_euler_content_bridge_target.md)
pins the required bridge and explicitly records this type/owner mismatch.
This is an open mathematical target, not a formal consequence of ρ4 or the
ρ5 iff.

### Gate normal form and Route W strip landed (records 1508–1509, 2026-09-16)

Two formal bricks execute the formal layer of the preregistered order of
battle in record 1503 section 6. Record [1508](../proofs/1508_r3_gate_ambient_normal_form.md)
(`C1G8R3GateAmbientNormalForm`) proves the gate normal form: the single
square-sum `(★) Summable ‖(J† C J)(e_i)‖²` is equivalent, for any named
pair of bases, to Hilbert–Schmidt columns of the ambient
projection-conjugate `P ∘L C ∘L P` — by `P = J J†` the conjugate is the
lifted detector precomposed by `J†`, and both directions are single
applications of the committed square-sum transfer. The gate is now one
explicit ambient operator's HS membership. Record [1509](../proofs/1509_route_w_strip_hs.md)
(`C1G8R3RouteWStripHilbertSchmidt`) proves the Route W strip lemma: for
every bounded window placement the compressed strip operator (the
record-1495 mechanism with free parameters `(A, C, d, e)`) has
square-summable columns on any ambient basis, and the `P`-post-composed
strip keeps them. The tail composition remains the irreducible phase-typed
remainder (record 1505); the Hardy-pressure finding of record 1503 governs
any tail estimate. Acceptance logs `0916_gate_ambient_try3.log` (3956 jobs)
and `0916_route_w_strip_try2.log` (3213 jobs), both zero-error with the
three standard axioms and zero `sorryAx`. The gate, ρ4 GIVEN (★), the ρ5
iff GIVEN (★), the ρ5 Euler-content bridge, and RH remain open. RH not
claimed.
