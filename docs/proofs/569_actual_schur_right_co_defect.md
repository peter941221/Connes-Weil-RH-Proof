# Proof 569: Actual Schur Right Co-Defect

## Result

For an actual rectangular Schur step with old frame `F₀`, new frame `F₁`,
ambient transport `Z`, and transition

```text
T = F₀† Z F₁,
```

the reverse row orientation has the exact Gram decomposition

```text
I - T† T
  = F₁† (I - Z† Z) F₁
    + Rᵣ† Rᵣ,

Rᵣ = (I - F₀ F₀†) Z F₁.
```

The second term is a genuine positive boundary leakage term.  It measures the
part of the transported new-frame range that leaves the old-frame range.  It
is not the same object as the left co-defect `I - T T†` and does not identify
the transition with an isometry.

For the actual Schur owner, the source carries the exact intertwining

```text
Z F₁ = F₀ T.
```

Therefore the transported new-frame range is already inside the old-frame
range, and the boundary channel vanishes exactly:

```text
Rᵣ = (I - F₀ F₀†) Z F₁ = 0.
```

The actual right co-defect consequently reduces to the compressed ambient
defect

```text
I - T† T = F₁† (I - Z† Z) F₁.
```

Whenever `Z†Z <= I`, the same operator is also the genuine Julia Gram factor

```text
I - T† T = F₁† D_Z† D_Z F₁,
D_Z = (I - Z† Z)^(1/2).
```

This is the exact bridge from the reverse transition defect to the ambient
Julia defect slot used by the range-sine ledger.

The source also proves the corresponding pointwise quadratic readout without
manually changing the order of a complex inner product:

```text
‖D_Z (F₁ x)‖² = Re⟪(I - T† T)x, x⟫.
```

Lean obtains this by first proving the operator-level Gram identity
`(D_Z ∘ F₁)† (D_Z ∘ F₁) = I - T† T`, then applying Mathlib's
`apply_norm_sq_eq_inner_adjoint_left` to the whole composite. This keeps the
right orientation explicit and does not identify it with the left co-defect.

## What This Closes

The source Schur step now has a Lean owner for the right co-defect required by
the raw reverse row.  The proof uses only the old/new frame isometries, the
Hilbert adjoint, and the idempotence of the old-frame orthogonal projection.
The actual-source specialization also proves the boundary channel is zero and
exposes the compressed form through
`suffixActualSchurTransitionRightCoDefect_eq_compressed_ambient`.
The generic Julia factor is exposed by
`rectangularTransitionRightCoDefect_eq_frameAdjoint_canonicalJuliaDefect`;
the pointwise readout is exposed by
`rectangularTransitionRightCoDefect_inner_eq_canonicalJuliaDefect_normSq`.

## What Remains Open

This identity is an exact decomposition, not a uniform estimate.  It does not
control the signed raw transition skew from Proofs 567--568, and it does not
provide the relative Douglas bound needed for Gate 3U.  In particular, the
right co-defect cannot be substituted for the packed physical left defect. The
zero boundary channel is a consequence of the exact source intertwining; it is
not a proof that the two transition orientations agree.

Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurRightCoDefect.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurRightCoDefectAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

## Verification

The Windows source was copied to the Ubuntu-24.04 WSL2 ext4 mirror before
building:

```text
focused source lake build: 3339 jobs, pass
focused audit: pass; eleven audited declarations use exactly
  [propext, Classical.choice, Quot.sound]
CCM25Concrete aggregate: 3838 jobs, pass
full repository: 3919 jobs, pass
```

The localhost-proxy warning and existing repository linter warnings are
environmental or pre-existing. No `sorry`, `admit`, or user axiom was added.
