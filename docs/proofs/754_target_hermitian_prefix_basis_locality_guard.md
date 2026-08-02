# Proof 754: Target Hermitian Prefix Basis-Locality Guard

## Result

Proof 753's Hermitian prefix identity is exact, but it is only a consumer of
a future estimate. Its prefix basis is an arbitrary Hilbert basis of the
source Sonin carrier; it carries no spatial locality, compact-root, or
boundary-kernel contract.

Therefore compact-root support cannot by itself be transferred to the
ordered finite-prefix trace. The missing theorem must control the complete
physical scalar with the inserted source prefix projection, or must bypass
prefixes and estimate the full root-relative signed trace directly.

This is a route guard. It proves neither Gate 3U nor any finite-S sign.

## Code Evidence

The Proof 753 owner accepts the basis as an unconstrained parameter:

~~~lean
noncomputable def sourceTargetHermitianPrefixCompressionTrace
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : ℂ :=
  Matrix.trace (basisPrefixMatrix sourceBasis N
    (finiteEulerTargetHermitianResponse owner lambda family))
~~~

Source:
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSGatePhysicalTargetHermitianPrefix.lean:178.

The generic prefix matrix has only matrix coefficients:

~~~lean
noncomputable def basisPrefixMatrix {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ) (operator : H →L[ℂ] H) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ⟪basis (i : ℕ), operator (basis (j : ℕ))⟫_ℂ
~~~

Source:
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSMovingBandPrefixCompression.lean:33.

Neither definition contains a support projection, a root convolution, or a
condition on the ambient image of the rank-N prefix projection.

## Why Trace Legality Is Not Enough

For every positive integer n, let

~~~text
H_n = C^(2n)
A_n = diag(1, ..., 1, -1, ..., -1)
P_n = projection onto the first n standard basis vectors.
~~~

Then A_n is self-adjoint and trace class, with

~~~text
Tr(A_n) = 0,
Tr(P_n A_n P_n) = n.
~~~

Thus even a zero full trace of a self-adjoint trace-class operator gives no
uniform bound on ordered prefix traces. The issue is not an
infinite-dimensional trace cycle: it is already present in finite matrices.

In a separable Hilbert space, a rank-N subspace can be placed in the first N
coordinates of some Hilbert basis. Consequently, an abstract basis parameter
does not give the ambient operator

~~~text
J P_N J*
~~~

any compact-root localization. Here J is the source Sonin inclusion and P_N
is the source basis-prefix projection.

## Consequence for Proof 753

Proof 753 correctly proves

~~~text
Tr(P_N H_S P_N)
  = sum_(i < N) Re(K_S(e_i)),
H_S = (L_S* W J + J* W L_S) / 2.
~~~

The equality identifies the right scalar. It does not make the finite-rank
factor P_N compatible with the compact-root support in [W, R]. The
fixed-family trace-class theorem only lets a proved prefix bound pass to the
ordinary trace; it cannot create that bound.

The valid source alternatives are:

1. Construct one named source basis together with a real-line localization
   theorem for every inserted J P_N J*, while retaining the complete outer,
   reflected second-support, and prolate scalar before its first absolute
   value.

2. Estimate Re Tr(T_S) directly on the existing root-relative signed
   physical owner, without passing through arbitrary basis prefixes.

The first option requires a new source-specific geometric theorem. The
second is the existing complete signed-trace route. A generic
self-adjointness, trace-class, Hilbert-basis, or finite-dimensional cyclicity
argument supplies neither option.

## Relation to Existing Guards

Proof 242 already prevents relabeling an abstract complete basis as the
route's concrete Mellin rows. Proof 388 prevents replacing a genuine Julia
contraction prefix with an abstract unitary cocycle. The present guard is
separate: it concerns the source-basis prefix introduced by Proof 753 after
the physical full-kernel scalar has been identified.

No Lean source or audit changes are made for this documentation-only guard.

## Current Literature Check

The arXiv Atom API query dated 2026-08-02 returned the new preprint

https://arxiv.org/abs/2607.24830v2

Its abstract describes a numerical finite-element realization of Suzuki's
operator and explicitly says that it does not prove RH. It supplies neither a
uniform semilocal signed-trace estimate nor a prefix-localization theorem.

The same query returns CCM24's Zeta zeros and prolate wave operators as
version 2:

https://arxiv.org/abs/2310.18423v2

Its abstract proves semilocal Sonin stability and describes a future prolate
candidate. It does not supply the complete relative-displacement estimate
needed for Gate 3U. No current primary source found in this narrow query
changes the required source theorem above.
