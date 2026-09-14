# 012 — G8 same-owner readback: conditional RH reachability audit

**Status:** supporting technical route audit, 2026-09-14. This record does
not alter the binding route ruling in [003](003_b1_b5_minimal_exit_route_selection.md),
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

At present the tower exports the healthy test, support window, and visible
prime cutoff (`C1P2DefectControl.lean:644-647`), but it does not export a
named lower-data G8 geometry package. Defining that package and proving its
projection from the existing orbit construction is the first formal
packaging task. It is a compatibility task, not the missing sign theorem.

## 4. Milestones and stop rules

| Stage | Required delivery | Current evidence | Stop rule |
| :-- | :-- | :-- | :-- |
| R0 | Define raw `OrbitG8Geometry g` and prove that the pinned tower construction exports it without mentioning a sign conclusion | support/visible-prime fields are formal; the geometry package is absent | If the only available source for a required field is a healthy/sign proposition, the producer is circular and stops |
| R1 | Instantiate the canonical owner and `g8CanonicalFamily` on the raw geometry; state all scale and basis choices explicitly | owner equality and canonical family are formal | If a cutoff construction changes `sourceTest`, square, or prime family, it is a route mismatch and stops |
| R2 | Prove a finite-cutoff same-owner trace identity with a named remainder | positive cutoff and selected-support residual decompositions are formal | An identity that reads a different response, basis, or prime support does not count |
| R3 | Prove remainder convergence and the trace-to-`qw` limit, giving `G8SameOwnerReadbackData` | open; P1 column-energy, transport, endpoint, and P2 residual limits are the recorded dependencies | A bound that uses a pre-assumed `qw` sign, RH, or a universal gate is circular and stops |
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
