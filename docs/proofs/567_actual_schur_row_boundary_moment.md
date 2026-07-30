# Proof 567: Actual Schur-Row Boundary-Moment Telescope

## Result

The named Schur row from Proof 566 now has a concrete source-level telescope.
For every adjacent visible-prime/suffix pair, the Schur forward coframe is
annihilated by the source complete-Sonin projection, and the four-term row is

```text
named Schur row
  = Schur boundary moment at S * transition†
    - transition† * Schur boundary moment at p :: S.
```

The two moments are built from the exact named Schur forward and endpoint
coframes on the same source carrier.  No physical coframe is silently
identified with them.

## What This Closes

This removes the remaining source-carrier and orientation ambiguity in the
named Schur row.  The four physical terms can be handled as one telescoping
object before any norm is taken.

The same module also exposes the transition mismatch exactly:

```text
Euler transition - actual Schur transition†
  = oldFrame† * (physical Euler transport - actual Schur transport†)
    * newFrame.
```

This is a real residual, not a notation choice.  The packed Julia analysis
column controls the actual Schur co-defect, so the displayed transport gap
must be absorbed by the signed row before a Douglas estimate can be claimed.

The raw row itself uses the adjoint transition.  Its exact gap is therefore

```text
Euler transition† - actual Schur transition†
```

and the named row is split using this adjoint gap.  The two displayed gaps
are related by taking the adjoint, but they are not interchangeable as
operator compositions.

The named row is now explicitly split as

```text
named row
  = actual-Schur boundary-moment coboundary
    + transition-gap coboundary.
```

## What Remains Open

The theorem does not factor either signed coboundary through
`suffixEulerFrameAmbientBoundaryAnalysis`.  In particular, it does not prove
the relative Douglas estimate

```text
||named Schur row† x||^2
  <= C^2 ||leftCoDefect x||^2.
```

The endpoint metric coframe and the adjacent transition still require a
source estimate that preserves the signed coboundary.  Injectivity of the
ambient loss column and contractivity of the Schur transition do not imply
this relative estimate.

Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurRowBoundaryMoment.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurRowBoundaryMomentAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```
