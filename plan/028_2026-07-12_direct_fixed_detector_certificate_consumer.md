# 028 Direct Fixed-Detector Certificate Consumer

Date: 2026-07-12

Status: rejected as an executable route by Plan 036/proof 114. The local owner
and Burnol formula survive; no finite-S positive producer survives.

## Idea

Bypass `ConcreteCCM25ArithmeticPackage` and its hidden
`ForAllTests` certificate. For one Xi/M4 detector `f` and one cutoff `lambda`,
use only:

```text
FinitePrimeExact.ExactSupportAtLambda W f f lambda
source_square_qw_reads_square
the fixed-test pole normalization
the fixed-test finite-prime normalization
```

The consumer must be rewritten to accept a local certificate for the same
square instead of a global `CCM25Interface` package.

## Required gates

1. Prove the fixed-test exact support for the genuine ambient convolution square
   from compact log support.
2. Prove the local prime/pole formula without importing
   `FixedLambda...CertificatesForAllTests`.
3. Rebuild the QW sign bridge so it consumes this local certificate directly.
4. Transport the CC20 trace and M4 bad-space sign to the same `f`.
5. Check that no final theorem or bridge still imports the broad package.

## Cheap death gate

Search the intended consumer for any `CCM25Interface`,
`ConcreteCCM25ArithmeticPackage`, or `SourceRouteTraceData` premise. If the
consumer cannot be generalized to a fixed-test certificate without reusing one
of those broad structures, Plan 028 is dead as well.

The current blast-radius audit finds the broad package embedded throughout
`Route/Bridge.lean`; do not patch individual constructors. Build a parallel
`FixedDetectorWeilData` and first prove a standalone detector contradiction.
See proof 096.

The standalone type probe now compiles without the broad package. See proof
097. The next death gate is whether the Xi detector can fill its local source
fields without importing the universal rows.

The repository already supplies the missing local finite-prime support through
`SelectedWeilSquareOwner` and `SelectedWeilFormulaOwner`; see proof 107. Plan
028 should use this owner rather than reconstructing a broad package.

The next root is now explicit: no theorem identifies
`SelectedWeilFormulaOwner.weilValue` with the source-zero sum of the same test.
See proof 108.

Exact consumer audit: the existing `SourceQWEqualsNegCC20WeilSum` structure
contains no numerical equality. The decisive equality is a separately stored
`NormalizedRouteBackedYoshidaLocalSumReadOff`. Plan 028 must prove a fixed-test
version of that equality from CC20, not merely rebuild arithmetic fields. See
proof 098.

Correction: the old exact equality is itself the wrong target because `K_I`
survives triple vanishing. The fixed-detector consumer must prove a strict
inequality after M4 bad-space orthogonalization and carry finite-prime/pole
terms on the same square. See proof 099.

Burnol's classical explicit formula has now been aligned term by term with
`SelectedWeilFormulaOwner`: the centered half-density substitution matches the
pole and prime terms exactly, and the apparent archimedean integral difference
is canceled by the `log(4)` constant shift. See proof 109 and Plan 032.

This does not authorize route Lean. The decisive gate is now semilocal: the
archimedean M4 compact remainder controls a prime-free window, while the
growing Xi-quotient cutoff sees finite primes. Plan 028 survives only if one
obtains either a strict negative detector in a fixed prime-free window or a
source-backed finite-S main-term subtraction with a genuine `-2 Id + compact`
post-Q remainder and the correct coefficient for every prime power.

Final executable verdict: the prime-free branch is impossible on the M4
complement (proof 113); the endpoint metric and log-Poisson positive owners fail
the prime-power/read-off gates (proofs 042 and 111); and CCM24 contains no
finite-S sign theorem (proof 112). Reopening requires the new same-object
contract in Plan 036.
