# 957 - Wall-A 1.4 arch half is genuine (not a 0-dodge) - route ruling

Date: 2026-08-10.  Status: route finding (definitions read; not a new proof).
RH NOT claimed.

## Claim

On the concrete healthy carrier the SCAL relation is

    2*totalArchimedean(convolution f) + (globalSum - restrictedSum) = 0

and this CANNOT be closed by assuming totalArchimedean = 0 for the route
common test, because the arch term is genuinely non-zero there.

## Why

- totalArchimedean F = if Nonempty { g : CompactLogTest // g.test = F } then
  compactLogArchimedeanTerm (choice) else 0.  (CompactArchTotal)
- CompactLogTest is just any Schwartz test with HasCompactSupport (a test field plus a compactSupport proof).  (CompactLogConvolution)
- The healthy convolution is SchwartzMap.convolution (CompactLogTest.convolution
  is the same MeasureTheory convolution).  The common test has compact support
  (ConcreteP1SupportProbe.commonBump_support_subset).
- Hence common*common also has compact support, so there IS a CompactLogTest
  with .test = convolution(common,common); totalArchimedean there =
  compactLogArchimedeanTerm (the real CCM25 Eq.3.7 value), not 0.

## Consequence

Closing Wall-A 1.4 on this carrier requires verifying the genuine analytic
identity compactLogArchimedeanTerm(convolution) = -(global-restricted)/2,
which is real analysis (Weil explicit formula).  It is NOT an algebraic or
definitional equality.  Status on Wall-A 1.4: structural half closed and
verified (ScabLhsZero, docs/956); analytic half open (this ruling).

RH NOT claimed.  See also docs/952 (target), 954 (row2), 956 (LHS zero).
