# 1088 - endpoint literature and C3 interface audit

Date: 2026-09-01. Corrected after the claim-strength audit of record 1087.

Status: binding companion to the route ruling in
[`003`](003_b1_b5_minimal_exit_route_selection.md). This record classifies the
ROOT endpoint and the detector-specific semi-local interface. It proves no new
analytic sign and does not claim RH.

## 1. Evidence levels

Every status below uses one of three labels:

```text
FORMAL
    Proved by a Lean declaration whose premises and axiom audit are named.

LITERATURE-BACKED
    Stated in a cited paper. The project still owes an exact convention bridge
    and, where required, a Lean or independently checkable certificate.

NUMERICAL
    Observed in a finite computation. It may guide theorem design but cannot
    close a route, retire a construction, or establish a continuum sign.
```

Record
[`1087`](../proofs/1087_c3_root_window_spectral_verdict.md) is NUMERICAL. Its
negative finite-matrix eigenvalues are not certified variational bounds: the
moment constraints use floating-point quadrature and SVD, and the zero-extended
sine profiles do not belong to the smooth `CompactLogTest` carrier. Even a
certified exact finite subspace would give only a lower bound for the continuum
supremum, not the upper bound needed for a no-go theorem. The scan does not
change the binding route.

## 2. C3 has two branches

The active B5 argument starts by assuming a nontrivial zero off the critical
line. The two required signs must concern the same healthy `CompactLogTest`:

```text
assume an off-line zero rho
          |
          +--> detector branch
          |      choose g with HealthyYoshidaDetectorData rho g
          |      hence qw(g) = spectralWeilValue(F_g) < 0
          |
          +--> semi-local positivity branch
                 prove 0 <= qw(g) for that same g
                 and its finite visible prime-power set
                            |
                            v
                       contradiction
                            |
                            v
                         SourceRH
```

The detector branch is FORMAL. The theorem
[`exists_healthyDetectorData_of_sourceNontrivialZero_right`](../../ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean#L511)
constructs such a `g` for a right-hand representative of every hypothetical
off-line zero. The construction uses a convolution orbit; its exported theorem
does not bound the final support by the ROOT window or by `[-0.8,0.8]`.

The semi-local positivity branch is OPEN. The exact minimal consumer is now
formalized as

```lean
(hsemiLocal : ∀ rho : sourceNontrivialZeroSet,
  (1 / 2 : Real) < rho.1.re →
    ∃ g : CompactLogTest,
      HealthyYoshidaDetectorData rho.1 g ∧
        0 ≤ C1SameOwnerWeil.qw g) →
  RHDefinitionBridge.standard.SourceRH
```

by `healthy_sourceRH_of_right_detector_specific_qw_nonneg`. This is only the
contradiction wiring. No theorem currently produces the `0 <= qw g` field for
the orbit detector.

## 3. Sign bookkeeping at ROOT and beyond

For every triple-vanishing healthy test, Lean proves

```text
qw(g) = -archimedeanTerm(F_g) - finitePrimeSum(F_g),
F_g = g.convolutionSquare.
```

Evidence:
[`qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple`](../../ConnesWeilRH/Dev/C1HealthyYoshidaDetector.lean#L114).

At ROOT support, `finitePrimeSum(F_g)=0`, so

```text
qw(g) < 0  iff  archimedeanTerm(F_g) > 0,
qw(g) >= 0 iff  archimedeanTerm(F_g) <= 0.
```

At a larger orbit window, visible prime powers generally remain. The
corresponding conditions are

```text
qw(g) < 0
  iff archimedeanTerm(F_g) + finitePrimeSum(F_g) > 0,

qw(g) >= 0
  iff archimedeanTerm(F_g) + finitePrimeSum(F_g) <= 0.
```

Therefore the orbit-window problem is not "the same archimedean gate at a
larger radius." The arithmetic term is part of both signs. The existing
`HealthyYoshidaDetectorData` already supplies the strict negative side; C3 owes
the opposite semi-local inequality on the same object.

## 4. Current brick status

```text
+------+-----------------------------------------+----------------------------------+
| ID   | Obligation                              | Status                           |
+------+-----------------------------------------+----------------------------------+
| E1   | Paper-scale finite-section/Toeplitz      | OPEN in Lean;                    |
|      | certificate near lambda > 1             | LITERATURE RECONSTRUCTION        |
+------+-----------------------------------------+----------------------------------+
| E2   | Prolate owner, Appendix-F tail, exact    | OPEN in Lean;                    |
|      | Fact-1 bound, equation-(100) slope       | LITERATURE RECONSTRUCTION        |
+------+-----------------------------------------+----------------------------------+
| E3   | Theorem-7 same-owner ROOT trace identity | OPEN in Lean;                    |
|      | and ROOT positivity                     | LITERATURE RECONSTRUCTION        |
+------+-----------------------------------------+----------------------------------+
| D1   | Right-oriented orbit detector with       | FORMAL                           |
|      | qw(g) < 0                               |                                  |
+------+-----------------------------------------+----------------------------------+
| P1   | Finite visible-prime crossing and trace  | FORMAL readback infrastructure;  |
|      | ownership                               | no sign                          |
+------+-----------------------------------------+----------------------------------+
| P2   | 0 <= qw(g) for the same orbit detector  | OPEN                             |
+------+-----------------------------------------+----------------------------------+
| Exit | D1 + P2 imply SourceRH                  | FORMAL implication               |
+------+-----------------------------------------+----------------------------------+
```

The finite-prime infrastructure is substantial but not a positivity theorem.
In particular:

- [`ordinaryTraceAlong_selectedEulerLogBoundaryPairOperatorSum_eq_finitePrimeTerm_sum`](../../ConnesWeilRH/Dev/C1SelectedDetectorSemiLocalEulerBoundary.lean#L270)
  reads a finite visible Euler boundary back to its prime-power sum.
- [`ordinaryTraceAlong_projectionResponse_eq_visibleEulerSum_add_residual`](../../ConnesWeilRH/Dev/C1SelectedDetectorSemiLocalResidual.lean#L108)
  retains an explicit residual.
- [`selectedEulerBoundaryResidual_eq_prolate_sub_compression`](../../ConnesWeilRH/Dev/C1SelectedDetectorSemiLocalResidualDecomposition.lean#L117)
  decomposes that residual into two geometric channels and asserts no sign.

Thus P2, not the arithmetic coefficient bookkeeping, is the unresolved
mathematical step.

## 5. The ROOT endpoint interface

The current ROOT-local endpoint package is

```lean
structure CC20EndpointTraceCertificate (g : CompactLogTest) where
  coefficient : Real
  trace : Real
  trace_nonnegative : 0 <= trace
  endpoint_bound :
    trace - cc20RankOneBadDirection coefficient g <=
      cc20WInfinityLog g.convolutionSquare
```

For a triple-vanishing root-supported `g`, this certificate yields `0 <= qw g`.
The rank-one term vanishes at the zero node, and the square is prime-free. See
[`qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf`](../../ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean#L133).

The helper
[`zeroTraceCertificate_of_nonnegative_wInfinity`](../../ConnesWeilRH/Dev/C1CC20EndpointCertificateData.lean#L161)
shows that a proof of scalar `cc20WInfinityLog >= 0` is enough to package the
current interface once an exact in-band gamma datum is supplied. This reduces
the amount of operator data needed for the ROOT interface; it does not extend
the certificate to orbit support or account for visible primes.

The root-window interpolation theorem is also narrower than a detector theorem.
[`exists_pinnedHealthyDetector_rootWindow`](../../ConnesWeilRH/Dev/C1HealthyDetectorPinning.lean#L91)
provides triple vanishing, nonzero detection, support, and an empty visible
prime set. Its sign remains the separate premise
`selectedDetectorArchimedeanGate`. Calling this object a "pinned detector" is
repository terminology; it is not yet `HealthyYoshidaDetectorData`.

## 6. External compact-window result

[Marcus Chuk, arXiv:2608.24827](https://arxiv.org/abs/2608.24827), submitted
2026-08-25, is an unreviewed preprint. Corollary 9 states

```text
Q(f) >= 8.9e-18 * ||f||_2^2
```

for every complex `f in L2(R)` supported in `[-0.8,0.8]`. In that paper `Q(f)`
is the full Riemann-Weil quadratic form of the original test `f`; its geometric
formula includes the pole, archimedean, and prime terms. It is not merely an
archimedean form applied to an independently supplied square.

The result is potentially relevant in two different ways:

1. A ROOT-supported project test fits inside `[-0.8,0.8]`. After an exact
   convention bridge, Corollary 9 could replace the E1--E3 ROOT positivity
   producer.
2. It would close P2 for the orbit detector only if the selected detector were
   proved to have support inside `[-0.8,0.8]`. No such support theorem is
   currently exported.

The required import bridges are:

```text
+----+-------------------------------------------+----------------------------+
| ID | Required bridge                           | Status                     |
+----+-------------------------------------------+----------------------------+
| M1 | Identify the paper's f with the healthy   | OPEN                       |
|    | CompactLog log-coordinate test            |                            |
+----+-------------------------------------------+----------------------------+
| M2 | Prove Q(f) = qw(g), including Fourier,     | OPEN                       |
|    | Mellin, involution, scale, and sign        |                            |
+----+-------------------------------------------+----------------------------+
| M3 | Transfer the L2/support/admissibility      | OPEN                       |
|    | hypotheses                                |                            |
+----+-------------------------------------------+----------------------------+
| M4 | Package ROOT scalar positivity into the    | FORMAL helper exists       |
|    | current endpoint certificate              |                            |
+----+-------------------------------------------+----------------------------+
| M5 | Reproduce or formalize the interval        | OPEN                       |
|    | certificate used by Corollary 9           |                            |
+----+-------------------------------------------+----------------------------+
| M6 | Bound the selected orbit detector inside   | OPEN; required only for    |
|    | [-0.8,0.8]                                | direct use on P2           |
+----+-------------------------------------------+----------------------------+
```

The preprint is therefore a plausible endpoint supplier, not a landed project
theorem. M1--M5 would address the ROOT local base. P2 additionally needs M6 or
a genuinely semi-local positivity theorem at the detector's actual support.

Primary sources:

- Connes--Consani, *Weil positivity and Trace formula, the archimedean place*:
  <https://arxiv.org/html/2006.13771>
- Chuk, *Weil positivity in compact windows: certified two-sided bounds and a
  Landau--Widom decay law*: <https://arxiv.org/html/2608.24827>

## 7. Binding conclusion

C3 is not complete. The negative detector branch and the contradiction wiring
are formal. The missing theorem is detector-specific semi-local nonnegativity
for the same orbit-supported `CompactLogTest` and its finite visible prime
powers.

Record 1087 neither closes the ROOT alternative nor forces an orbit-window
route change. The active route remains the healthy-`CompactLog`, B5-shaped
route selected by record 003. New work must target P2 directly or prove a
support-and-convention bridge that lets a valid compact-window theorem supply
P2 for the selected detector.
