# 2169 — Root-window positive-direction screen corrected

Date: 2026-09-29.

Status: **SCOPED NUMERICAL NO-GO; no producer Go.** The screen serves the
healthy detector consumer

```text
selected detector has qw < 0 (ICgate > 0 on the pole-free class)
  -> prove qw >= 0 for that same owner -> SourceRH.
```

The tested owner class was a real smooth-bump span supported in the centered
root window `[-log(2)/2, log(2)/2]`, with the three exact Laplace constraints
at `0, 1/2, 1` and the detection normalization
`laplaceAt(g, 0.6 + 14.134725141734693 i) = 1`.  This is an auxiliary
finite-dimensional owner, not the selected closed-ball owner.  The premise
under test was a positive Archimedean quadratic form after the three node
constraints.

## Correction

Record 2168 reported a positive null direction.  Its cross-basis `F(0)` term
used `b_i(-x)b_j(x)` for translated bumps instead of the self-correlation
`b_i(x)b_j(x)`.  That error manufactures a positive direction.  Record 2169
uses the direct autocorrelation formula and polarizes the quadratic form from
the same evaluator.  For the normalized affine fibre, the independent
`numpy.convolve` and FFT reads agree to at most `3.6e-15`.

At 28 bump functions, the nullspace of the three node constraints plus real
and imaginary detection constraints has top eigenvalue

```text
dx = 0.002 : -0.0062324257638
dx = 0.001 : -0.0060688291764
```

The least-norm detection-normalized point has Archimedean values
`-0.6676400918` and `-0.6704947162`, respectively.  Every sampled affine
null direction remains negative; the detection value stays `1 + O(10^-13)`.
The artifact is `results/2169_root_window_positive_candidate.json` and the
reproducer is `scripts/root_window_positive_candidate_2169.py`.

## Independent basis check

The sine basis screen in records 1022/1700 was re-read with 24 basis
functions, radius `0.345`, 1800-point Gauss constraints, 641 profile terms,
and an 8001-node direct grid.  Its constrained Arch spectrum is

```text
reference: [-2.84066623, -0.859369832]
direct:    [-2.84387587, -0.859127186]
```

The `3.227e-3` reference/direct difference is far below the negative margin.
The prior short-grid positive reading was therefore an evaluator/indexing
artifact, not a root-window candidate.

## Wider-window follow-up

Adding the actual finite prime-power terms and scanning sine spans at radii
`0.6, 0.7, 0.8, 0.9, 1.0, 1.2, 1.5, 2.0, 2.5, 3.0` did not produce a
positive constrained `ICgate` eigenvalue.  The largest readings were between
`-2.40e-4` and `-4.89e-4` after halving the grid step at the tested radii;
the `r=1.0, K=24` row moved from `-4.392e-4` at `dx=.001` to
`-2.364e-4` at `dx=.0005`.  This is only a screen, not a continuum no-go;
the finite-prime evaluator, endpoint smoothness, and complete owner transfer
remain open.

## Decision

Freeze the cheap “root-window positive Arch direction” branch under this
owner and basis family.  Reopen only with a named change: a proved
non-sine smooth source family, a different support/owner, or a certified
finite-prime quadratic form whose top eigenvalue has a strict positive margin.
This record does not change the binding B5 route, does not transfer any sign
to the selected detector, and makes no RH claim.
