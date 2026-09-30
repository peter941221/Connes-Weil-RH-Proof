# 2274 - Route A analytic multiplicity bound

Date: 2026-09-30
Status: hmult proved and consumed

## Result and remaining scope

The new Lean module proves

```text
completedRiemannXi(2) = pi/3
spectralMultiplicityConstant <= 128.65 <= multProxy2248
spectralMultiplicityConstant < 128.70692502980964
```

The producer consumer
`a005_item5_producer_wired_certified_multiplicity` supplies this proof
internally. It keeps the same pair of compact-log tests, the same
high-shell sum, and the existing tail and signed-margin constants. Its
remaining hypotheses are hstrip, hmargin, hcharge-rest, and hgap. The
original conditional consumer remains available for existing callers.
This removes one producer premise. It proves neither selected-owner
positivity nor RH.

## Normalization correction

The project defines `completedRiemannXi(s) = s (s-1) Lambda(s)` away
from the poles, where Lambda is the completed zeta function. Standard xi
has an additional factor 1/2. At s = 2, Mathlib's zeta special value and
Gamma factor give

```text
zeta(2)       = pi^2/6
GammaR(2)     = 1/pi
Lambda(2)     = pi/6
project xi(2) = 2 Lambda(2) = pi/3
standard xi(2)= Lambda(2)   = pi/6
```

The 2273 audit substituted standard xi into the project formula. Record
2274 withdraws its under-rounding interpretation and its claimed
3.54e-13 margin. The original artifact remains in the superseded file;
the corrected diagnostic reports both normalizations. The formal
original-proxy theorem proves that the earlier decimal was already safe.
The slightly increased constants remain valid and do not need another
ledger change.

## Analytic bound

A single-sided bound is an inequality proved in the safe direction; it
need not reproduce every decimal of a function value. The following
bounds suffice for the existing consumer:

```text
+-------------------------------------------+----------------+
| Component                                 | Proved bound   |
+-------------------------------------------+----------------+
| Gamma(1/4)                                | <= 37/10       |
| (1/pi)^(1/4)                              | <= 19/25       |
| kernelSmallMomentConstant                 | <= 703/250     |
| completedRiemannXiKernelTailConstant       | <= 19/9        |
| abs(log(norm(project xi(2))))             | <= 1/20        |
| log(2)                                    | >= 693/1000    |
+-------------------------------------------+----------------+
```

For Gamma, log-convexity means the value between two positive arguments
is at most their weighted geometric mean. Apply Mathlib's multiplicative
convexity inequality at 2 and 5/2 with equal weights. The midpoint is 9/4.
The half-integer formula gives Gamma(5/2) = 3 sqrt(pi)/4. Two uses of
Gamma(x+1) = x Gamma(x) transport this bound back to 1/4. Rational pi
and square-root bounds then give Gamma(1/4) <= 37/10.

For the kernel tail, the first seven nonnegative exponential-series
terms at 3 exceed 19. Since pi > 3, exp(pi) >= 19, and hence
2/(1-exp(-pi)) <= 19/9. For the xi logarithm, pi/3 > 1 fixes its sign;
log(x) <= x-1 and pi < 3.15 give the bound 1/20. Mathlib's certified
log-two bound implies log(2) >= 693/1000.

The final rational arithmetic assembles

```text
fixed <= 2 (19/9) (703/250 + 1)
constant = (fixed + 73 + abs(log(norm(project xi(2))))) / log(2)
constant <= (2 (19/9) (703/250 + 1) + 73 + 1/20) / (693/1000)
         <= 128.65
         < 128.70692502980964
         < 128.70692502981
```

No numeric artifact supplies a premise in this proof. Mathlib supplies
the zeta special value, Gamma recurrence and log-convexity, pi bounds,
exponential-series inequality, and log inequalities. These are borrowed
classical ingredients; this record claims no original zeta or Gamma
identity.

## Reproduction and evidence

Owning module: `ConnesWeilRH/Dev/C1RouteAMultiplicityBound.lean`.
Paired axiom audit: `ConnesWeilRH/Dev/C1RouteAMultiplicityBoundAudit.lean`.
Producer probe: `ConnesWeilRH/Dev/C1RouteAProducerWiredProbe.lean`.

Build the analytic leaf, its producer consumer, and the root aggregate:

```text
lake build ConnesWeilRH.Dev.C1RouteAMultiplicityBoundAudit ConnesWeilRH.Dev.C1RouteAProducerWiredProbe ConnesWeilRH
```

Run the corrected numeric diagnostic and its regression tests:

```text
python scripts/routea_weighted_zero_multiplicity_proxy_audit_2273.py
python scripts/routea_multiplicity_proxy_selftest_2273.py
```

The Lean proof, rather than the diagnostic digits, supplies hmult. The
numeric artifact binds its source files by LF-normalized SHA-256 hashes
and records its mpmath version and precision. The original consumer
remains an API-compatible conditional form; the new consumer has no
hmult argument.

Validation outcome: the owning module, paired audit, producer probe, and
root aggregate finish with `Build completed successfully (4244 jobs)`
in `build-logs/2274_final_build.log`, with no error lines. All ten new
analytic audit declarations and five producer probe declarations report
exactly `[propext, Classical.choice, Quot.sound]`. The corrected
multiplicity regression suite passes seven tests. The Linux strip control
suite passes all 22 tests including the actual anchor-failure injection.

The first strip integration attempt refused the changed consumer sources
because their old manifest hashes no longer matched. The reviewed refresh
binds 126 files, adding the analytic supplier and its two owner-definition
modules. The successful replay retains sup 6663660.437141987, margin
1.426584561481876, and CERTIFIED-STRIP-COVERED. A full field comparison
against the committed 2267 artifact finds changes only in provenance and
input-validation metadata; numerical rows and anchors are unchanged.
The preserved 2273 superseded artifact is byte-identical to the original
committed diagnostic.

## Next unresolved obligation

The analytic hgap enclosure is now the first unresolved item in map 104.
It must bound the actual ideal-to-discrete functional difference, not a
measured refinement delta. After that, the strip envelope still needs a
formal certificate, and the selected owner's signed qw >= 0 remains the
producer's mathematical endpoint.
