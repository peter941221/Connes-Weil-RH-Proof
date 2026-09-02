# 1099 - the C3 exit composition (the formal remainder is one Prop)

Date: 2026-09-02.

Status: record 1089 pinned the orbit detector and named the orbit-window
semi-local gate; this record lands the composition that makes the gate the
ONLY remaining formal content of the C3 branch.  RH is not claimed.  Evidence
labels follow map `004` section 1.

## 1. The brick

`ConnesWeilRH/Dev/C1OrbitWindowExitComposition.lean` (+ paired audit):

- `qw_nonneg_of_healthyDetectorData_of_orbitWindowSemiLocalGate`: the
  pointwise composition.  `HealthyYoshidaDetectorData` carries the
  triple-vanishing field `vanishesOnF`, which is exactly the extra premise
  the record-1089 bridge `qw_nonneg_of_orbitWindowSemiLocalGate` needs, so
  the gate alone upgrades any healthy detector to `0 <= qw g`.
- `sourceRH_of_orbitWindowSemiLocalGate` (HEADLINE): the gate, assumed for
  every healthy orbit detector of every hypothetical right-hand off-line
  zero, implies `RHDefinitionBridge.standard.SourceRH`.  The proof composes
  the record-1089 pinned object (healthy data AND window AND visible-prime
  bounds), the bridge, and the already-formal contradiction consumer
  `healthy_sourceRH_of_right_detector_specific_qw_nonneg`.  The off-line
  hypothesis needed by the pinned-object headline follows from
  `(1/2 : Real) < rho.1.re` by `linarith`.

Build evidence: `build-logs/1099_exit_composition_build2.log`,
`Build completed successfully (3635 jobs)`, zero `error:` lines, and both
declarations print exactly `[propext, Classical.choice, Quot.sound]` (zero
`sorryAx`).  One iteration: the first audit file tripped the 100-character
linter on its own `#check`/`#print` lines; fixed by using the bare names
under the already-open namespace.

## 2. What this changes in the route bookkeeping

Before this record the C3 branch had two named open parts: exhibit the
detector (FORMAL since record 1087/1089) and prove semi-local positivity on
it (OPEN).  The headline collapses the second part onto the pinned first
part: no detector-design freedom is left anywhere in the formal statement.
The entire remaining C3/P2 content is the single universal Prop

```text
forall rho off-line right,
  forall g healthy for rho,
    orbitWindowSemiLocalGate g
      -- archimedeanTerm F_g + finitePrimeSum F_g <= 0,  F_g = g.convSq
```

and one line of already-formal wiring separates it from `SourceRH`.

## 3. What this record does not do

It does not prove the gate, does not constrain the sign in any window, and
does not touch the S2 producer chain (records 1095/1098) or GATE 1.  The
numerical pricing of the gate over the triple-vanishing subspace at orbit
radii is a separate, pre-registered investigation (record 1100).
