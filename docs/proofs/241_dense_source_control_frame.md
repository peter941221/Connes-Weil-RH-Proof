# Proof 241: Dense-Source Control Frame

Date: 2026-07-14

Status: accepted as an axiom-clean lower producer and finite-row consumer
contract.  The finite-S sign and the source-frame span coverage remain open.

## Result

`CompactBadSpace` now has a data-bearing compactness theorem:

```text
exists_finite_source_controlFrame
```

For a compact continuous operator `K`, a positive threshold `c`, and any
`DenseRange source`, it returns a finite set `sourceFrame` such that

```text
sourceFrame is finite
sourceFrame <= range(source)
Re <x,Kx> <= c ||x||^2  on (span sourceFrame)^perp.
```

The proof takes a `c/2` net of the compact image of the unit ball and chooses
one source value within `c/2` of every net center.  The two triangle-inequality
errors therefore add to at most `c`.  Scaling the unit-vector estimate gives
the arbitrary-vector bound.

The following corollaries preserve the source-span witness and shift the form
by `c`:

```text
exists_finiteDimensional_controlSpace_spanned_by_denseRange
exists_finiteDimensional_remainder_nonpositive_spanned_by_denseRange
exists_finiteDimensional_remainder_nonpositive_on_evaluationSpace_spanned_by_denseRange
```

The finite-row consumer is also explicit:

```text
exists_finite_source_controlFrame_with_finite_row_vanishing
```

If `span(sourceFrame) <= span(rows)` and every row satisfies
`inner x (rows i) = 0`, then the shifted quadratic form is nonpositive.  The
coverage condition is an input, not a conclusion.

## Concrete CC20 Instance

`RegularKernelHaarCompact.lean` instantiates the source family as

```text
ContinuousMap.toLp 2 cc20CompactHaarMeasure ℂ
```

and discharges its dense range with Mathlib's
`ContinuousMap.toLp_denseRange`.  It exports both

```text
exists_finiteDimensional_cc20HaarRegularRemainder_nonpositive_on_continuous_inputs
exists_finite_cc20HaarRegularRemainder_nonpositive_on_finite_row_vanishing
```

for the actual compact operator
`cc20CompactHaarComplexL2Operator`.  No normalized route predicate, source RH
assumption, finite-prime trace identity, or detector coverage proposition is
used by these declarations.

## Why This Is Lower

The old compact theorem selected arbitrary vectors from a finite net.  Such a
space could not be connected to exact Mellin/Yoshida rows without an
untracked change of witness.  Proof 241 selects nearby values of one named
dense source family and keeps the finite set in the conclusion.  This removes
that witness mismatch while leaving the genuine hard obligation visible:

```text
actual finite-S detector row span
             >=
compact remainder's source frame
```

Density alone cannot prove this finite-dimensional containment.  In
particular, do not read the theorem as a finite-S positivity result or as a
replacement for the negative Yoshida owner.

## Verification

The Windows snapshot was copied one way into a new WSL2 ext4 mirror because
the persistent mirror was dirty.  The following commands passed under the
repository Lake lock:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete.CompactBadSpace

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete.RegularKernelHaarCompact

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.DenseSourceControlFrameAudit
```

The import-facing audit contains `#check`, `#print`, and `#print axioms` for
all new generic and concrete declarations.  Every audited declaration reports
only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx` or project axiom appears.  `git diff --check` is clean apart from
the repository's existing CRLF normalization notices.

## Route Judgment

```text
dense-source compact frame: accepted in Lean
finite-row orthogonality bridge: accepted in Lean
concrete CC20 continuous-input instance: accepted in Lean
actual finite-S row-span coverage: open
finite-S remainder sign: open
active RH roots removed: no
RH: unproved
```

The next producer must prove the displayed row-span coverage for the same
negative Yoshida/CC20 object, rather than adding another abstract compactness
wrapper.
