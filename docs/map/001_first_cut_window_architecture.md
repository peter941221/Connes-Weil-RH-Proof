# 001 — ROOT-window architecture and boundary

Status: shared local base; partially formal; not an RH exit.

Authority: binding for work that uses the CC20 ROOT window, the
`gamma + alpha/beta + delta` endpoint chain, or paper-scale Toeplitz/prolate
certificates. The healthy-owner route ruling remains [003].

## Purpose

The first-cut theorem concerns tests supported in the fixed ROOT window

```text
[-log(2)/2, log(2)/2].
```

That support condition removes visible prime powers and turns the local Weil
functional into the CC20 Archimedean endpoint problem. It does not cover the
selected orbit detector, whose support and finite prime set depend on the
hypothetical off-line zero and the chosen orbit index.

## Owner boundary

```text
ROOT-local test
  -> CC20 endpoint positivity on the fixed window
  -> useful local input only

selected healthy detector
  -> support-derived finite visible-prime set
  -> detector-specific semi-local positivity
  -> SourceRH
```

There is no automatic arrow between these rows. A future use of the ROOT
theorem must name either a support theorem placing the actual selected test in
the ROOT window or a semi-local extension that includes its exact prime set.

## Formal assets retained

The repository contains checked infrastructure for:

- translation and root-support bookkeeping;
- the endpoint coefficient and certificate data owners;
- finite-dimensional quadratic-form and LDL certificate ingestion;
- the first Hilbert-space spectral-decomposition lemma;
- raw/windowed displacement kernels and their L2/Lp operator bounds;
- Archimedean, pairing, and windowed readbacks;
- pointwise-diagonal owner guards preventing replacement of the actual kernel
  by a formally easier but inequivalent one.

Principal modules include `C1CC20TranslateInvariance.lean`,
`C1CC20RootWindowOperator.lean`, `C1CC20EndpointCertificateData.lean`,
`C1CC20FiniteDimensional.lean`, `C1YoshidaLdlCertificate.lean`,
`C1CC20OperatorGap.lean`, `C1CC20DisplacementKernel.lean`, and their paired
Audit modules. Detailed declaration chronology is preserved in Git history
and the corresponding proof records.

## Open endpoint package

The local endpoint theorem still requires a same-owner chain containing:

1. a paper-scale finite-section/Toeplitz certificate at the actual published
   scale near `lambda > 1`, including the exceptional direction, complement
   spectral bound, and rank-one repair;
2. the concrete prolate owner, Appendix-F uniform tail, exact Fact-1 L1
   certificate, and equation-(100) slope identity;
3. the Theorem-7 trace identity on that owner;
4. the resulting ROOT-window endpoint positivity theorem.

The audit correction that must not be lost is that equation (119) includes
the central `n = 0` term and the published scale is above one. The existing
`lambda < 1` Bessel lower bound is therefore only a side branch.

## Deferred autocorrelation bridge

The Titchmarsh square-form bridge from a generic compactly supported test to
an autocorrelation square is deliberately deferred. A classical proof needs
Paley–Wiener/Cartwright entire-function machinery not currently present in
Mathlib. It is not needed for the detector-specific B5 shape and must not be
used to reopen universal B1 globalization.

## Admission rule for future work

A new theorem on this local chain is admissible only if its statement names a
consumer in the healthy detector-specific semi-local route. A theorem ending
only at fixed-window positivity, density, or all-test globalization remains
local infrastructure and is frozen by [003].

Evidence classification: the listed Lean infrastructure is `FORMAL`; the
remaining endpoint package is a mixture of `LITERATURE-BACKED` source facts
and `PROJECT CANDIDATE` formalization obligations. RH is not claimed.
