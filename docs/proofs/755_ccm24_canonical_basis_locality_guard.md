# Proof 755: CCM24 Canonical-Basis Locality Guard

## Result

The natural CCM24 cyclic basis is not a missing locality producer for Proof
753. It supplies a canonical spectral ordering, not a compact spatial
localization of the inserted prefix projection.

```text
CCM24 cyclic vector / orthogonal polynomials
                 |
                 v
canonical spectral basis candidate
                 |
                 X  no source theorem gives spatial locality of J P_N J*
                 v
compact-root prefix estimate
```

This closes only that proposed repair. It does not prove that no localized
Sonin basis can ever be constructed, and it does not prove Gate 3U, the
finite-S sign, Burnol's identity, or `_root_.RiemannHypothesis`.

## Lean Evidence

Proof 753 accepts an unconstrained basis:

```lean
(sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
```

The prefix matrix records only matrix coefficients:

```lean
noncomputable def basisPrefixMatrix ...
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ) (operator : H ->L[ℂ] H) :=
  fun i j => ⟪basis (i : ℕ), operator (basis (j : ℕ))⟫_ℂ
```

Sources:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalTargetHermitianPrefix.lean:202-221

ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSMovingBandPrefixCompression.lean:29-33
```

Neither declaration has a spatial support predicate, a root factor, or a
condition on the ambient range of `J P_N J*`. This is the formal reason Proof
754 rejected arbitrary Hilbert-basis prefixes.

## CCM24 Candidate And Its Limitation

The closest natural replacement is CCM24's cyclic construction. The primary
source states that the scaling operator with its Gaussian cyclic vector is put
in canonical form by orthogonal polynomials, and that the Hardy--Titchmarsh
transform maps Hermite functions to those polynomials. The same paper states
that the semilocal map `theta_S` is a bounded invertible hilbertian
isomorphism of Sonin spaces.

Primary source:

```text
Connes, Consani, Moscovici, "Zeta zeros and prolate wave operators",
arXiv:2310.18423v2, pp. 3-5 and Theorem 4.6 on pp. 22-23.
https://arxiv.org/pdf/2310.18423v2
```

The candidate is globally spectral, not spatially local. Already at the
archimedean starting point, the first cyclic/Hermite vector is a Gaussian. It
is nonzero at every real coordinate. Its rank-one projection has kernel

```text
K_0(x, y) = h_0(x) * conjugate(h_0(y)),
```

which has full spatial support in `R x R`. Therefore its prefix projection
does not itself carry the finite-window property needed to insert a compact
root into the Proof 753 prefix trace.

The semilocal transport does not repair this automatically:

```text
bounded invertible map
  -> transports a closed Sonin subspace
  -/-> preserves support of vectors or finite-rank projections.
```

CCM24 Theorem 4.6 proves the former. It does not state the latter. The
existing project carrier guard makes the same distinction: a Gram-corrected
projection may transport a range, but an oblique or bounded-invertible
transport is not an orthogonal spatial projection.

There is a further interface gap. CCM24's cyclic construction is an ambient
spectral construction. The current Lean prefix consumes a basis of
`sourceSoninCarrier lambda`. Turning the former into the latter would itself
require a named restriction/completion theorem, and a later Gram--Schmidt or
orthogonal-complement step cannot be assumed to preserve spatial locality.

## Consequence

The following implication is unsupported and must not be used:

```text
CCM24 canonical cyclic basis
  -> source Sonin Hilbert basis
  -> localized J P_N J*
  -> compact-root ordered-prefix estimate.
```

The missing source theorem would need all three concrete parts:

```text
1. a named Hilbert basis of the actual source Sonin carrier;
2. a spatial kernel or support statement for every J P_N J*;
3. a bound for the complete outer + reflected-second-support + prolate scalar
   after that localization and before the first absolute value.
```

Until such a theorem exists, the valid route is the existing direct signed
trace:

```text
outer compact-root branch
  + reflected second-support/prolate branch
  -> one complete relative-displacement scalar
  -> compact support before the first absolute value
  -> uniform Gate 3U estimate.
```

The source currently gives the first branch's compact-root geometry and the
second branch's Hardy--Titchmarsh/prolate decomposition. It does not give a
common relative-displacement kernel for their sum.

## Verification

This is a documentation-only source audit. The code references above were
read directly, and the CCM24 claims were checked against the primary arXiv PDF
on 2026-08-02. No Lean source or audit changed, so no WSL2 build is required.
