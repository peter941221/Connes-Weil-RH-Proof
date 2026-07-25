# Proof 540: raw co-defect factor

Result: good. This closes the bookkeeping gap between Proof 538's raw
Douglas domination and an actual right factor through the adjacent
left co-defect. It does not prove the raw Douglas estimate, Gate 3U, the
finite-S sign, Burnol's identity, or RH.

## What it is

The new Lean module is
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawCoDefectFactor.lean.
It introduces SuffixRawCoDefectFactorData with the exact operator orientation

    rawDefect = leftCoDefect ∘ rightFactor.

Here rawDefect is the recombined raw four-term adjacent defect
suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S, and
leftCoDefect is the actual adjacent Julia co-defect stored in
(suffixEulerFrameSchurStep lambda p S).leftCoDefect.

## Why it matters

Proof 538 leaves the active estimate in Douglas form:

    ||rawDefect† x||^2
      <= C^2 *
         (||ambientLossColumn x||^2 + ||boundary† x||^2).

Proof 505's physical ledger identifies the summed channel energy with the
actual left-co-defect energy:

    ||ambientBoundaryAnalysis x||^2 = ||leftCoDefect x||^2.

Therefore the raw Douglas estimate is not merely a factor through an
auxiliary product carrier. It is equivalent to an honest right factor through
the same adjacent co-defect that downstream kernel guards consume.

## How Lean proves it

The construction uses the generic Douglas factorization theorem
exists_factor_of_norm_sq_le with

    A = rawDefect†
    B = leftCoDefect.

The produced factor is first an adjoint-side map. Taking adjoints and using
self-adjointness of the canonical Julia co-defect gives the desired source
orientation:

    rawDefect = leftCoDefect ∘ rightFactor.

Lean also proves the reverse implication: any such bounded right factor
implies the original raw Douglas domination with the same bound.

The resulting equivalences are:

    single suffix:

    raw Douglas domination
      <-> Nonempty raw co-defect factor data

    uniform family:

    uniform raw Douglas domination
      <-> Nonempty uniform raw co-defect factor data

    existence level:

    exists finite uniform raw Douglas bound
      <-> exists finite uniform raw co-defect factor bound

## Guard retained

Every successful right factor still passes the zero-mode test:

    leftCoDefect x = 0
      -> rawDefect† x = 0.

So Proof 539's obstruction remains the correct safety check. A nonzero raw
adjoint on the left-co-defect kernel rules out this factorization exactly as
it rules out the original raw Douglas estimate.

## Verification

The Ubuntu 24.04 WSL2 ext4 verification batch passed:

    Proof 540 source module      3329 jobs, PASS
    Proof 540 focused audit      3330 jobs, PASS
    CCM25Concrete aggregate      3810 jobs, PASS
    full repository              3891 jobs, PASS

All eight audited principal declarations use exactly
[propext, Classical.choice, Quot.sound]. The new source and audit contain no
sorry, admit, or user axiom declaration and have no line longer than 100
characters. Existing repository linter warnings remain unchanged. The WSL
localhost-proxy notice is external.
