# 2273 — Route A multiplicity proxy rounding correction

Date: 2026-09-30

## Finding

The independent high-precision diagnostic places the former record-2248
decimal `multProxy2248 = 128.70692502980964` below the real expression
used by Lean. The 100-digit evaluation gives

```text
spectralMultiplicityConstant  128.706925029809646157520238638184...
old proxy                    128.706925029809640000000000000000...
old proxy - exact            -6.157520238638...e-15
```

The diagnostic identifies an unsafe rounding direction in the former
`hmult` target. It does not formally prove the reverse inequality.

## Correction

The Lean ledger now uses

```text
multProxy2248     128.70692502981
highShellTail2248 4894093747.7643
```

The corrected proxy is above the independently evaluated exact expression by
about `3.5384e-13`. The high-shell tail is rounded upward again so the
arithmetic consumer remains monotone and safe.

## Scope

The correction fixes the direction of the numeric target. It does not close
`hmult`: a formal analytic upper bound for the Gamma, exponential, pi, and
xi-at-two terms is still required. The audit script is diagnostic evidence,
not a Lean certificate.

## Verification

- script: `scripts/routea_weighted_zero_multiplicity_proxy_audit_2273.py`;
- artifact: `results/2273_multiplicity_proxy_audit.json`;
- Lean target: `ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean`;
- status: `OLD-PROXY-UNDER-ROUNDS`;
- regression suite: `python scripts/routea_multiplicity_proxy_selftest_2273.py`,
  five tests passed; precision controls at 60, 100, and 140 digits preserve
  the rounding direction, and the corrected rational tail covers its product;
- owning arithmetic module, producer consumer, and producer probe:
  `Build completed successfully (3524 jobs)`, no lines beginning `error:`;
- all four producer probe declarations report only
  `[propext, Classical.choice, Quot.sound]`;
- no producer GO, no gate sign change, no RH claim.

The artifact records SHA-256 hashes of the three Lean source files after
normalizing line endings to LF, records the mpmath version, uses
a local precision context, and reports failure through a nonzero exit code
if the registered diagnostic outcome changes. The xi-at-two evaluation
uses `completedRiemannXi(2) = pi/6`; Lean must still check that identity
before the diagnostic formula can supply an analytic comparison.

## Next proof target

The corrected proxy leaves approximately `3.54e-13` of numerical margin.
Closing `hmult` at this proxy requires one-sided formal bounds for the
kernel tail, small Gamma moment, absolute logarithm of xi at two, and a
positive lower bound for `log 2`. A high-precision decimal table alone
cannot supply those bounds.

First establish the xi-at-two identity from the completed-zeta definition
and Mathlib's `riemannZeta_two`. Then prove rational bounds on the four
components and assemble the numerator and denominator monotonically.
If the tight Gamma enclosure costs more than the tail ledger needs,
evaluate a coarser formally provable proxy against the unchanged owner
and signed-margin budget before changing the consumer. This record does
not implement that alternative or remove any producer premise.
