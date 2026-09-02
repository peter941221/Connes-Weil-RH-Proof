# 1076 - B1/B5 minimal exits and the single healthy-owner mainline

Date: 2026-08-31.

Status: route ruling. RH is not claimed.

Map role: binding route ruling. New work must serve the healthy-`CompactLog`,
B5-shaped chain stated here unless a later record in `docs/map/` explicitly
replaces this decision. The endpoint-certificate scope and provenance labels
are maintained by [`004`](004_endpoint_literature_interface_audit.md).

## Decision

The output audit has two singleton logical cuts:

```text
{B1} -> RH
{B5} -> RH
```

These cuts do not describe equal proof campaigns.  The project will pursue one
B5-shaped campaign on the healthy `CompactLog` owner.  The B1-only universal
generalization is frozen.

The active dependency graph is:

```text
assume an off-line zero rho
          |
          +--> orbit detector g with qw(g) < 0       [formal]
          |
          +--> 0 <= qw(g) for the same g and its
                 finite visible prime-power set      [open]
                            |
                            v
                         SourceRH                    [formal implication]
                            |
                            v
                 Mathlib RiemannHypothesis

ROOT-window CC20 positivity                          [local base, open in Lean]
          |
          +--> usable only after proving that the selected g lies in its
               support class, or after extending the certificate semi-locally
```

The ROOT package is a local base, not a predecessor that automatically applies
to the orbit detector. It does not close B1 or B5.

Terminology guard: `B1` and `B5` in this record are the output-audit cuts.
Record 1074's older phrase "GATE 1 alpha B1" names only the bounded
`n >= 2` arithmetic brick for equation (983).  New plans call that brick
`alpha-(983)-tail`; it is not the B1 exit.

## Lean evidence for the singleton cuts

For any inhabited C1 input data, the skeleton proves the B1 criterion
equivalent to Mathlib RH:

```lean
theorem normalizedCoreCC20PropositionC1SourceCriterion_iff_mathlibRH_of_inputData
    (input : WeilPositivityInput)
    (hdata : CC20PropositionC1InputData ... input) :
    CC20PropositionC1SourceCriterion ... input ↔
      _root_.RiemannHypothesis
```

`ConnesWeilRH/Dev/WeilC1NonEmptyProducer.lean` constructs such input data.
The B1 root supplies the criterion for every input, so B1 alone reaches RH.

The route layer proves the B5 coverage socket equivalent to Mathlib RH after
using the landed normalized detector-existence theorem:

```lean
theorem normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_mathlibRH
    (hexists : CC20YoshidaDetectorExists ...) :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage ↔
      _root_.RiemannHypothesis
```

See `ConnesWeilRH/Dev/UnconditionalSkeleton.lean` and
`ConnesWeilRH/Route/CC20RouteRealization.lean`.  These equivalences establish
the logical cuts.  They do not supply sound analytic producers for either cut.

The healthy owner now also has the exact minimal B5 implication:

```lean
(∀ rho : sourceNontrivialZeroSet,
  (1 / 2 : Real) < rho.1.re →
    ∃ g : CompactLogTest,
      HealthyYoshidaDetectorData rho.1 g ∧ 0 ≤ C1SameOwnerWeil.qw g) →
  RHDefinitionBridge.standard.SourceRH
```

This is theorem `healthy_sourceRH_of_right_detector_specific_qw_nonneg` in
`C1HealthyYoshidaSpectralNegativity.lean`. The same file constructs the strict
negative detector for every hypothetical right-hand off-line zero. The only
missing part of this implication is the matching `qw g >= 0` producer.

## Evidence for the quantifier boundary

CC20 Theorem 1 assumes support in `[2^(-1/2), 2^(1/2)]`.  In log
coordinates the test lies in `[-log 2/2, log 2/2]`.  The landed Lean consumer
has the same scope:

```lean
(hsupport : Function.support g.test ⊆
  Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)) →
0 ≤ C1SameOwnerWeil.qw g
```

See `ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean`, theorem
`qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf`.

CC20 Appendix C equation (155) quantifies over every compactly supported smooth
test and sums all places:

<https://arxiv.org/html/2006.13771>

Splitting a long-support test into ROOT-sized pieces creates mixed terms in the
quadratic form and exposes new prime powers.  No landed theorem controls those
terms.  Record 1050 names this gap and rejects a density lift.

## Why B5 is the selected shape

A natural B1 producer must prove the finite-vanishing sign for all compactly
supported tests.  A B5-shaped producer needs the sign only for the detector
chosen against one hypothetical off-line zero.  It may use the detector's
support radius to select a finite set of visible primes.  The second obligation
has fewer sign cases and does not require a universal partition theorem.

This comparison ranks the targets; it does not prove that B5 has a positivity
producer. The orbit detector with `qw(g) < 0` is formal, but the theorem exports
no ROOT or `[-0.8,0.8]` support bound. Record 1087 reports only floating-point
finite-matrix values at ROOT support and proves no continuum sign. Numerical
hunting does not change either statement.

## Owner correction

The literal socket
`normalizedSelectedFinalRouteDetectorCriterionCoverageRoot` remains useful for
the output axiom audit.  Lean proves it RH-equivalent in
`ConnesWeilRH/Route/CC20RouteRealization.lean`.

New mathematics must not target its normalized owner.  The underlying
`normalizedCC20TestSpace` defines the alleged convolution square through the
old additive test algebra.  The axiom-clean theorem
`not_normalizedCC20MellinConvolutionLaw` proves that this operation doubles a
Mellin value instead of multiplying Mellin values.  Record 016 rejects that
owner as a Yoshida/Weil producer.

The active route uses `CompactLogTest`, its genuine convolution square, and a
healthy-owner exit to `SourceRH`.  After such an exit is proved, the project can
retire, retype, or discharge the normalized audit socket without using it as a
premise.

## Freeze boundary

Allowed work must name one of these consumers:

1. a missing paper-scale field of the ROOT-local CC20 certificate;
2. an explicit support bound and finite visible-prime ownership for the formal
   orbit detector;
3. detector-specific semi-local positivity or its same-owner trace readback;
4. maintenance of the now-formal healthy-owner contradiction interface to
   `SourceRH`.

The following work is frozen:

1. universal B1 positivity over all compact supports;
2. density or partition lifts from the ROOT window;
3. new conditional owners for the normalized additive B5 socket;
4. numerical scans without a named theorem consumer.

This ruling supersedes diagrams that draw a direct arrow from fixed-window
CC20 positivity to the full finite-vanishing criterion.
