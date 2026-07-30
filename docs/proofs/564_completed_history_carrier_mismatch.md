# Proof 564: Completed History Is Not the Physical Endpoint

Proof 563 removed an exact zero-mode obstruction for the ambient loss column
on the actual source carrier. Proof 564 checks whether the existing completed
Schur history is already the physical completed-history readout needed by Gate
3U. It is not.

## Result

The existing completed history stores

```text
completed history
  = terminal survivor + metric rectangular boundary-dagger history.
```

The actual Schur endpoint uses a different boundary dagger. Its exact
decomposition is

```text
actual Schur endpoint
  = terminal survivor
    + metric boundary output
    + coherence boundary output.
```

The physical endpoint is related to that actual Schur endpoint by a second,
independent residual:

```text
physical endpoint
  = actual Schur endpoint + physical/Schur endpoint residual.
```

The new source theorem makes both missing terms explicit:

```text
source physical endpoint coframe
  = upper Euler factor * (
      terminal survivor output
      + metric boundary-output sum
      + coherence boundary-output sum)
    + physical/Schur endpoint residual.
```

Here the terminal survivor output is the existing transition-product readout
through the parameterized Sonin Gram inverse square root. The two boundary
lists have the same length as the visible-prime list, and their sum is an
exact continuous-linear-map identity.

## What This Closes

The Lean development now proves:

```text
metric boundary output + coherence boundary output
  = actual-Schur boundary output,
```

and, after the Gram normalization,

```text
physical endpoint
  = survivor output
    + metric boundary output
    + coherence boundary output
    + endpoint residual.
```

This is an exact carrier and bookkeeping result. It prevents the old
completed-history consumer from silently reading the metric dagger as the
actual physical dagger.

## What This Does Not Close

No theorem in this batch proves that either residual is zero, has a sign, or
has a bound uniform in the finite visible-prime set. In particular, the batch
does not prove the Gate 3U estimate

```text
||gap(p,S)† x||^2 <= C^2 ||leftCoDefect(p,S) x||^2,
```

with one source-level constant `C` valid for every visible prime and suffix.
It also does not construct the corresponding uniform Douglas factor or prove
the finite-S sign, Burnol's identity, or RH.

The currently valid shortcut is therefore:

```text
completed history + existing per-step readouts
  -/-> physical Gate 3U readout.
```

The missing producer must either construct the actual physical readout with a
uniform bound, or prove the direct signed non-polar gap estimate and its
same-object readback. The two residuals must remain in that producer's signed
object; setting them to zero is not justified.

## Assessment

This is not a proof that the core estimate is impossible. Proof 563 found no
exact source-carrier kernel, and Proof 564 finds no source-level continuous
counterexample. The route is therefore still logically alive.

It is also not evidence that the estimate is close. The remaining issue is a
family-uniform analytic producer, not another algebraic telescope: approximate
kernels, the coherence output, and the physical-versus-Schur endpoint
residual still need a bound that survives the finite-S limit.

## Lean Evidence

Source:
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedPhysicalHistoryMismatch.lean`

Aggregate import:
`ConnesWeilRH/Source/CCM25Concrete.lean`

Focused audit:
`ConnesWeilRH/Dev/CCM24FiniteSCompletedPhysicalHistoryMismatchAudit.lean`

The central declarations are:

```text
suffixActualSchurBoundaryOutputMaps_sum_eq_metric_add_coherence
suffixActualSchurBoundaryOutputMaps_comp_gramInvSqrt_eq_metric_add_coherence
sourceActualBandForwardEndpointCoframe_eq_upperFactor_metric_coherence_add_residual
```

The audit prints exactly:

```text
[propext, Classical.choice, Quot.sound]
```

for every declaration in the new module.

Verification used the Ubuntu-24.04 WSL2 ext4 mirror and the following commands:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalHistoryMismatch
lake env lean ConnesWeilRH/Dev/CCM24FiniteSCompletedPhysicalHistoryMismatchAudit.lean
lake build ConnesWeilRH.Source.CCM25Concrete
lake build
```

Results:

```text
focused source build: 3300 jobs, pass
focused axiom audit: pass
CCM25Concrete aggregate: 3833 jobs, pass
full repository: 3914 jobs, pass
```

The repeated linter warnings and the WSL localhost-proxy warning are existing
environmental/tooling noise; no new build failure occurred.
