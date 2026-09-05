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
contradiction wiring. Record
[`1099`](../proofs/1099_c3_exit_composition.md) removes the last quantifier
slack on the formal side: its
`sourceRH_of_orbitWindowSemiLocalGate` composes the record-1089 pinned
object with the bridge `qw_nonneg_of_orbitWindowSemiLocalGate`, so the
entire remaining C3 content is the single universal Prop
`orbitWindowSemiLocalGate g` for every healthy orbit detector of every
hypothetical right-hand off-line zero (FORMAL reduction; the gate's sign is
the open part). No theorem currently proves the gate.

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
| P2   | 0 <= qw(g) for the same orbit detector  | OPEN; formal remainder is        |
|      |                                         | exactly `orbitWindowSemiLocal-   |
|      |                                         | Gate` on healthy orbit detectors |
|      |                                         | (record 1099, FORMAL reduction)  |
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

Formal admission audit (record 1140, 2026-09-05):
`C1T2Assembly.no_stageB_budget_of_qw_negative` proves that the existing
one-window Stage-B interface cannot manufacture its defect budget from the
already-formal detector negativity and a negative window certificate.  Since
`qw(g) < 0` gives `gate(g.square) > 0`, the assumptions
`gate(W.square) ≤ -mu`, `gate(defect) ≤ epsilon`, and `epsilon ≤ mu` are
inconsistent.  The theorem is FORMAL and uses the same-owner Weil identity
and exact defect identity only.  Consequently Stage-B remains an assembly
interface; P2 still needs an independent detector-specific defect inequality
controlling the archimedean integral and visible prime evaluations.

P2 control primitives (record 1140, extended 2026-09-05) are now FORMAL in
`C1P2DefectControl`: the exact finite visible-prime sum has a per-term norm
envelope, that envelope reduces to `2 * A` under a uniform defect-test bound,
and the singleton defect inherits `G + H` from detector/window square bounds.
An independent archimedean norm bound is also packaged.  These are producer
interfaces only; the true correction must still supply the concrete `A`, `G`,
`H`, zero-point, and integral bounds.
The combined finite-prime theorem
`abs_finitePrimeSum_defect_le_of_uniformSquareBounds` exposes the resulting
coefficient sum with `2 * (G + H)` directly to the Stage-B consumer.
The generic theorem `compactLogTest_norm_le_zeroSeminorm` supplies a canonical
uniform pointwise bound from the zero-order Schwartz seminorm, so the remaining
correction estimate may focus on bounding those seminorms and the archimedean
integral.
The support bridge `index_lt_of_support_subset_Icc` and its set-inclusion
companion now convert exported detector endpoints `[a,b]` into the explicit
finite cutoff `ceil(exp(max(|a|,|b|))) + 1` for `globalPrimeIndexSet`.
The convolution-square specialization symmetrizes the source interval and
transfers the same cutoff to `globalPrimeIndexSet g.convolutionSquare`, keeping
the finite visible-prime owner tied to the selected detector's support.
The canonical zero-seminorm specialization removes auxiliary pointwise-bound
hypotheses from the prime-side estimate and leaves only the two square
seminorms as concrete correction data.
The family theorem `defect_test_norm_le_of_uniformFamilyBounds` extends this to
the actual finite Stage-B sum, with defect norm bounded by
`G + Σ |λᵢ| Hᵢ` under per-window pointwise bounds.
The combined consumer `abs_ICgate_defect_le_of_uniformFamilyBounds_and_arch`
now turns this into an explicit full defect-gate budget once an independent
archimedean bound is supplied; it assumes no gate sign or `qw` positivity.

Producer-primitive re-point (records 1097/1097b/1098, 2026-09-02): the S2
support chain's discharged primitive was re-adjudicated by the
pre-registered fork.  The record-1096 primitive A-in-HS (equivalently
`Tr K_S < inf`) is the raw-F1 quantity class that record 1063 falsified,
and the certified deep-octave probe confirmed the raw trace keeps its
power law (41.0499 at `xi_max = 204.8`, slope16x +0.335, no bend) while
the law-16 weighted legs stay O(1).  The canonical S2 primitive set is
therefore (a) `targetProlateDetectorAbsorbedFactorHS` (the absorbed
factor in Hilbert-Schmidt; witness: committed `p_hs` 3.5661 -> 3.5356,
O(1)) and (b) `targetProlateDetectorRootCommutatorTraceLegality`
(commutator-remainder legality; witness: committed `l_tr1` 1.3462 ->
1.2850, O(1)).  Record 1098
(`C1ProlateRootCommutatorAbsorbedLegalityDischarge.lean`, FORMAL, no sign)
wires the record-1095 consumer contract from (a)+(b); record 1096 is
demoted to a valid-but-unschedulable implication.  The verdict evidence
level is NUMERICAL (this record's section 1).

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
   proved to have support inside `[-0.8,0.8]`. For the committed fixed-window
   D1 orbit export this is IMPOSSIBLE, not merely unexported: the construction
   of `C1HealthyYoshidaUnscaledOrbit.lean` exports the support bound
   `Ioo (-(n+2)) (n+2)` (FORMAL, `n >= 0`), which always contains points of
   `|u|` in `(0.8, 2]`. Record
   [`1089`](../proofs/1089_orbit_certificate_extension_design.md) packages this
   support bound, the visible prime-power readback `q < exp(2*(n+2))`, and the
   orbit semi-local gate on one pinned object
   (`C1OrbitWindowSemiLocalGate.lean`, FORMAL, no sign). Sub-0.8-window orbit
   variants would face the record-1087 negative plateau (NUMERICAL,
   extrapolated beyond the scanned radius - reconnaissance, not verdict).

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
