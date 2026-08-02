# Proof 695: Complete coupled signed scalar owner

Date: 2026-07-31

Status: exact owner and truncation contract. This proof does not construct
the compact-support premise and does not close Gate 3U.

## Result

Proof 694 showed that the positive equal-leg Cauchy pair owns the defect
`C^dagger C`, not the signed boundary channel `C`. Proof 695 keeps the
complete physical target intact and packages the surviving signed scalar
readout at the route level.

The owner is:

~~~
structure SuffixCompleteCoupledSignedScalarOwner where
  routeOwner : SelectedWeilSquare.SelectedWeilSquareOwner
  target : RouteFiniteHorizonIndex ->
    sourceSoninCarrier unitSoninScale ->L[Complex] finiteSCarrier
  target_eq_complete : forall index,
    target index = routePrimeLogAdjointCoboundaryTarget routeOwner index
~~~

The equality field is the semantic guard. A consumer receives the complete
adjoint coboundary target, so it cannot silently substitute an outer branch,
reflected branch, second-support branch, or prolate term in isolation.

## Scalar readback

For a route index `index`, pair number `j`, source vector `v`, and detector
vector `u`, the owner exposes one scalar:

~~~
inner Complex
  (cc20GlobalLogTranslation ((2 * j : Nat) * Real.log index.prime) u)
  (signedOwner.target index v)
~~~

This is one coboundary readout. The target already contains
`(I - U_(-log p))` applied to the complete adjoint ambient target. Applying an
additional even-minus-odd difference here would create a second coboundary
and change the route object.

Lean proves both readbacks:

~~~
signedScalarPairedCorrelation = routePrimeLogPairedScalarCorrelation
signedScalarPairedCorrelation
  = inner (U_(2*j*log p) u) (routePrimeLogAdjointCoboundaryTarget v)
~~~

The existing route theorem still exposes the raw signed difference when a
consumer needs it. No physical branch is estimated separately.

## Compact-support contract

The source contract is deliberately a premise:

~~~
forall u v index, exists cutoff,
  forall j >= cutoff,
    signedScalarPairedCorrelation signedOwner index j u v = 0
~~~

Under that premise Lean derives eventual vanishing for the existing route
pair and proves, for every `N >= cutoff`,

~~~
sum (j in range N) signedScalarPairedCorrelation ...
  = sum (j in range cutoff) signedScalarPairedCorrelation ...
~~~

The equality is established before any norm, triangle inequality, or branch
wise estimate. This is the exact ordering required by the signed route; it is
not a proof that the actual complete owner has compact support.

## Files

Source:

`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSignedScalarOwner.lean`

Import-facing audit:

`ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSignedScalarOwnerAudit.lean`

Aggregate import:

`ConnesWeilRH/Source/CCM25Concrete.lean`

## Remaining bottom

Proof 695 does not provide the compact-support producer, a route-uniform
signed scalar bound, Gate 3U, the finite-S sign, the arithmetic same-object
trace identity, Burnol's identity, or `_root_.RiemannHypothesis`.

The next source theorem must identify the actual complete physical owner with
this scalar target and prove the signed cancellation or bound on the intact
coupled object.

## Verification

The Windows repository is the source of truth. Verification uses a fresh
Ubuntu-24.04 WSL2 ext4 mirror with the prior package cache reused.

Expected import-facing axiom output is exactly:

~~~
[propext, Classical.choice, Quot.sound]
~~~

No `sorry`, `admit`, user axiom, heartbeat increase, or recursion-limit
increase belongs to this proof.
