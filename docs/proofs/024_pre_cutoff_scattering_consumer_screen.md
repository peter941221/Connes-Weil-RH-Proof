# Pre-Cutoff Scattering Consumer Screen

Date: 2026-07-11

Status: the `eta_S` transport formulation is rejected. The direct fixed-S
conditioning formulation is also rejected under the current source-detector
consumer; its unresolved abstract operator theorem is not claimed false.

## Decision

The proposed `eta_S`-transport owner is not a new lane. Its genuine analytic
part is the operator layer already completed during Plan 012; its first
allegedly new fixed-S remainder identity is the semilocal transport gap that
the prior source audit rejected.

```text
source measure and scattering coordinate
  -> uncut scaling/Fourier representation
  -> one selected theta-smoothed commutator kernel
  -> square-integrability and ordinary trace of A* A
  -> exact local trace identity retaining D
```

The required consumer stops at the last line. In particular it must not assert
`D <= 0`, `D = 0`, a zero-sum sign, `SourceRH`, or a determinant/spectral
convergence claim.

## Fast Rejection

Plan 018's Suzuki defect is unsuitable: its half-line vanishing is RH
equivalent. Plan 019's Hilbert-complex proposal is unsuitable: an equivariant
differential cancels exact/coexact sectors in the supertrace, while the cutoff
needed for the CC20 kernel destroys that equivariance.

The pre-cutoff owner avoids both RH-level conclusions, but it is not novel. The
historical direct construction already proves the commutator Hilbert--Schmidt
estimate, produces the measurable `L2` kernel, and identifies the ordinary
positive trace. See `docs/proofs/cc20-012-mathematical-verdict.md:115-186` and
`:317-320`.

To extend this existing layer to the intended fixed-S identity retaining `D`,
one needs post-`Q` semilocal transport of derivative domains, orthogonal
projections, boundary evaluations, series tails, and endpoint-strip terms.
The prior audit proves that CCM24's `eta_S` is nonunitary and does not
intertwine the required operators; no checked source supplies these transport
equalities. See `docs/proofs/cc20-fixed-s-remainder-source-certificate.md`.

```text
eta_S transport to fixed S: rejected.
direct fixed-S definition through the unitary scattering phase u_S: possible.
```

The latter is not a free reopening. Its trace identity retains
`D_S o Q = <xi, (-2 Id + K_(S,I)) xi>`. The compactness argument rules out
vanishing on the natural infinite-dimensional triple-vanishing class. The only
remaining mathematical opening is a non-circular finite-codimension
conditioning theorem for the same detector test:

```text
xi orthogonal to the explicitly constructed positive eigenspace of K_(S,I)-2 Id
  -> D_S o Q(xi * xi*) <= 0.
```

That theorem must construct the detector and its orthogonality constraints
without detector coverage, `SourceRH`, or a stored zero-sum sign.

## Earliest Route Failure

Finite bad-space orthogonality is not the first death point. It adds only
finitely many linear conditions to the test. The first required condition that
is not local to the remainder is the strict source zero-sum sign of that same
test.

Plan 016 makes the dependency explicit: M5C must retain M5B's global tail
estimate and strict source zero-sum sign while adding the finite bad-space
conditions (`plan/016_2026-07-10_unified_remaining_gaps_plan.md:974-984`). M5B
requires a detector with epsilon-over-distance-squared control at every other
source zero (`:666-676`). This is precisely the P2 all-other-zero contract
rejected in Plan 023: after the `qeasy`/CC20 transfer it is an RH-level
detector-existence theorem.

Therefore the direct conditioning route cannot avoid the P2 death point:

```text
finite bad-space sign for D_S
  + same-test strict source zero-sum sign
  -> M5C

same-test strict source zero-sum sign
  -> M5B all-other-zero tail
  -> rejected P2 detector contract.
```

No choice of the finite positive eigenspace changes this implication. It can
repair the sign of `D_S`; it cannot manufacture the independent spectral sign
needed to contradict an off-line zero.

## Required API Boundary

```text
owner fields allowed:
  measure space and Hilbert realization
  uncut scaling and Fourier operators
  selected compact test and theta operator
  measurable kernel and L2 estimate
  ordinary trace of A* A
  source-normalized identity with the explicit remainder D

forbidden fields or conclusions:
  sign(D)
  vanishing(D)
  detector existence
  strict zero-sum sign
  SourceRH / RiemannHypothesis
```

The owner must be built before support/Fourier cutoffs are inserted. A later
cutoff may enter only as a selected bounded operator inside the trace identity;
it may not be used to define an allegedly scaling-equivariant differential or
to transport an orthogonal projection through CCM24's nonunitary comparison.

## Source And Code Evidence

Connes--Consani, *Weil positivity and the Trace formula, the archimedean
place*, `weil-compo.tex:755-808`, identifies the local remainder as

```text
D o Q(xi * xi*) = <xi, (-2 Id + K_I) xi>.
```

<https://arxiv.org/abs/2006.13771>

The result does not determine the sign of this form. That is exactly why the
consumer above stops at an explicit identity. The historical kernel evidence
is recorded in `docs/proofs/cc20-fixed-s-kernel-source-certificate.md`; the
no-defect equality is refuted in `docs/proofs/cc20-012-mathematical-verdict.md`.

## Final Verdict

```text
eta_S transport lane: dead.
direct fixed-S D_S conditioning route with the current source detector: dead.
reason: finite conditioning still requires M5B's all-other-zero sign, which
        is the rejected P2 RH-level detector contract.
abstract finite-codimension sign theorem alone: unresolved, but insufficient.
RH status: unchanged.
```

Do not create a wrapper around the completed operator/kernel facts. A future
direct fixed-S lane needs a new source-sign consumer that is strictly weaker
than M5B's all-other-zero detector theorem; adding spectral constraints to the
current detector cannot reopen it.
