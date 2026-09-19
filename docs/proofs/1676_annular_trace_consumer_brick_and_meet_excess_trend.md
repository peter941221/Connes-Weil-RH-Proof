# 1676 — The trace-form consumer brick: a uniform annular trace bound now reaches the survivor core

Date: 2026-09-19.

Status: one Lean brick + one F60-permitted trend rig. The S3 producer is
unchanged and OPEN; what changed is the INPUT INTERFACE of the consumers:
the uniform annular Gram upper bound can now be stated, proved, and consumed
entirely at trace level. RH is not claimed.

## 1. The gap this brick closes

After 1669/1670 (exact trace = column-energy identity), 1672 (trace-class
owners) and 1674 (trace positivity), the natural statement of the single
remaining S3 producer is the ordered estimate

```text
0 <= Re tr Gram(N,n) <= B     uniformly for n >= N.
```

But the committed square-sum consumers
(`sourceCompressedRoot_squareSum_of_eventual_annular_tsum_energy`,
`..._ambient_annular_tsum_energy`) accept only the column-energy tsum form.
A prover holding the trace form had no formal entry point. The new module
`Dev/C1G8R3AnnularTraceConsumer.lean` (+ paired Audit) closes the interface:

```text
sourceRootAnnularGram_column_energy_tsum_le_of_trace_le
  Re tr Gram(N,n) <= B   =>   (SUM' i, || ambient annular window e_i ||^2) <= B
                              [via the exact 1669 identity and the
                               Complex.ofRealCLM.map_tsum transport,
                               Complex.ofReal_re; idiom copied from the
                               1674 positivity proof]

sourceCompressedRootAnnularGram_column_energy_tsum_le_of_trace_le
  same for the compressed annular Gram/window pair.

sourceCompressedRoot_squareSum_of_eventual_ambient_annular_trace_bound
  (forall n >= N, Re tr ambient Gram(N,n) <= B)
      => Summable i, || sourceCompressedRoot owner lambda (basis i) ||^2
  [dispatches into the 1664/1669 ambient tsum consumer]

sourceCompressedRoot_squareSum_of_eventual_annular_trace_bound
  same for the compressed trace form.
```

Build: `build-logs/1676_annular_trace_consumer.log`, focused
`lake build ConnesWeilRH.Dev.C1G8R3AnnularTraceConsumer
ConnesWeilRH.Dev.C1G8R3AnnularTraceConsumerAudit`, footer
"Build completed successfully (3963 jobs)", zero `^error:` lines, zero
`sorryAx`; all four theorems depend only on
`[propext, Classical.choice, Quot.sound]`.

Consequence for the two-front accounting (map 044): row 1 of the table
(front A, the uniform annular Gram upper bound) is now FORMALIZABLE IN THE
TRACE FORM DIRECTLY, with both sides wired end to end.  The full
machine-checked chain from the open Pi statement to the gate:

```text
(forall n >= N, Re tr Gram(N,n) <= B)        <- the OPEN Pi statement
  => (THIS BRICK)   Summable i, || sourceCompressedRoot e_i ||^2
  => (1659 :369)    tendsto_g8EndpointSourceCutoffPairData_trace_of_
                    survivorCore consumes hcore in exactly this form
  => (1659 :336)    g8EndpointGate_iff_survivorCore (.mpr)
  =>                endpoint gate  <=>  SourceRH   (law F20)
```

Verified this round: `g8EndpointGate_iff_survivorCore`
(`Dev/C1G8R3ActualEndpointTraceLimit.lean:336`) consumes
`Summable fun i => || (J† C J) e_i ||^2`, which is definitionally the
`sourceCompressedRoot` form this brick's consumers conclude; and
`tendsto_g8EndpointSourceCutoffPairData_trace_of_survivorCore` (:369)
takes the same `hcore` hypothesis directly.  Every arrow except the first
is committed and audited.

## 2. The F60-permitted trend rig: meet-dimension excess

`scripts/annular_gram_trace_1676_trend.py`
(log `build-logs/1676_meet_excess_trend.log`) measures the one quantity F60
licenses — the meet dimension EXCESS over the forced count — for the model,
committed, and generic-random involutive phases at two grid resolutions,
with block dimension forced + 60 so the bound is saturated and the excess
is visible.

Calibration first (F27/F28): the forced count must be the EXACT lattice
count `dimE + dimQ - M`. At lambda = e^-1, L = 40:

```text
M = 4096:  du = 0.019531, k1 = 1997, k2 = 2099,
           dimE = 2099, dimQ = 2100, forced = 103, model meet = 103.
M = 8192:  du = 0.009766, forced = 205, model meet = 205.
```

Two consequences of the hand count:

- ERRATUM-GRADE CORRECTION to record 1675: the reported
  `forced_dim_reference = 102` was the float formula `int(2a/du)` rounding
  102.4 down; the exact lattice forced count is 103 (dimE and dimQ round
  asymmetrically). The dim-40 block readings of 1675 are unaffected
  (40 < 102 < 103).
- the m = 1 model meet EQUALS the forced count (no lattice point hits
  +-1), so `excess_model = 0` is the predicted calibration, and a generic
  random involutive phase also sits at the bound: `excess_random = 0`.
  The question is whether the committed phase separates from the random
  control.

## 3. Rig verdict: no separation — the committed phase has no grid-scale footprint, and the forced subspace is gap-isolated

```text
[M=4096 model]  accepted=103 excess=0  sigma_at_forced=3.65e-08  tail=0  drift=0
[M=4096 real]   accepted=103 excess=0  sigma_at_forced=3.44e-08  tail=0  drift=0
[M=4096 random] accepted=103 excess=0  sigma_at_forced=3.38e-08  tail=0  drift=0
[M=8192 model]  accepted=205 excess=0  sigma_at_forced=3.95e-08  tail=0  drift=0
[M=8192 real]   accepted=205 excess=0  sigma_at_forced=3.94e-08  tail=0  drift=0
[M=8192 random] accepted=205 excess=0  sigma_at_forced=3.38e-08  tail=0  drift=0
```

(accepted within tolerance 1e-8 on sigma; blocks of size forced + 60;
drift = last-Rayleigh drift over the final 100 iterations, exactly 0.)

Three readings, all control-consistent:

1. NO SEPARATION: the committed scattering phase, the m = 1 reflection,
   and a generic random involutive phase all sit EXACTLY at the forced
   count at both resolutions.  Any continuum-meet footprint of the
   committed symbol at these resolutions is bounded below sigma ~ 4e-8 —
   i.e. invisible.
2. GAP ISOLATION (new, sharper than 1675): past the forced subspace the
   Rayleigh spectrum falls to MACHINE ZERO (sigma^2 ~ 1e-15 at index
   `forced`, exactly 0 beyond).  There are no near-meet directions: on a
   truncated grid the carrier is either forced-meet or orthogonal to it.
   Whatever the continuum meet's shape, it casts no partial shadow — the
   continuum limit lives entirely in how the forced subspace DEFORMS as
   the grid refines, never in extra eigenvalues.
3. CALIBRATION HELD: excess_model = 0 as hand-predicted (no lattice point
   hits +-1), validating the exact-lattice-count method and the 102 -> 103
   erratum correction to 1675.

## 4. Laws

```text
F61  At saturated blocks (dimension >= forced + headroom) the truncated-
     grid meet sits AT the exact lattice forced count with a machine-zero
     spectral gap past it, identically for the committed scattering phase,
     the m = 1 model, and generic random involutive phases, across grid
     refinements.  The committed symbol has no grid-scale footprint; there
     are no near-meet directions on any truncated grid.  Together with F60
     this confines base numerics to quantities measured INSIDE a fixed
     ansatz subspace (as the 1640 Laguerre finite-section defect/mass
     quantities are) and forbids reading the meet itself on grids.
```

## 5. Boundary

The uniform annular Gram upper bound `Re tr Gram(N,n) <= B` is unchanged
and OPEN, as is the carrier base. The endpoint face consumes bounds at
trace level from this record on. RH NOT claimed.
