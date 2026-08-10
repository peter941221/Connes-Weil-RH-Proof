# 958 - Wall-A 1.4 Eq.3.7 arch/prime balance: numeric probe verdict

Date: 2026-08-10.  Status: numeric probe on a proxy test (NOT a proof; scoped).
RH NOT claimed.  See also docs/952 (target), 954 (row2=SCAL), 955 (mandatory),
956 (LHS zero), 957 (arch nonzero ruling).

## What was run

`docs/proofs/958_wall_a14_arch_probe.py` (mpmath, 80 dps).  It evaluates the
target scalar identity

    SourceScopedArchimedeanContributionBalance (SCB) targets
    2*arch(f*f) + (globalSum - restrictedSum) = 0

on a concrete smooth bump matching the route `commonBump` spec (smooth, compact
support in Icc (3/2)(5/2) on the log line, value 1 at 2; the real `commonBump`
is a `Classical.choose`, so this is a PROXY, not the exact route test).  It reads
`arch` exactly from the CCM25 Eq.3.7 def
`(log(4*pi)+eulerMascheroni)*(conv*conv)(0) + Integral_{y>0}[e^(y/2)(conv(y)+conv(-y))-2(conv*conv)(0)]/(e^y-e^-y) dy`
with `conv = f * f` (the compact convolution square the SCAL arch term reads).

## Results (convention-robust)

| piece | value (mpmath) |
|---|---|
| (f*f)(0) = ||f||^2 | +0.289113 |
| (log(4pi)+gamma)*(f*f)(0) | +0.898633 |
| arch integral | -0.604353 |
| arch (Eq.3.7) | **+0.294196** |
| 2*arch | **+0.588392** |
| finite side, log-convention (Connes-consistent: eval at log n) | +0.000043 ({2} only) |
| finite side, valueAt-convention (eval at n and 1/n) | **diverges** (partials 0.55/1.9/4.8/9.1/16/26) |

The `valueAt`-based atom (the `SourceFinitePrimitiveEvaluatorAtom` in
`PrimePowerArithmetic` = `vonMangoldt(n)/sqrt(n) * (value(f*f,n) + value(f*f,1/n))`,
with `value` = direct point evaluation) sees `conv(n)=0` for integer `n>=2`
(conv support is near 0) but `conv(1/n) ~ ||f||^2` for small `1/n`; its partial
sum `sum_{n prime-power <= N} Big(n)/sqrt(n)*conv(1/n)` grows unboundedly
(0.55 -> 1.9 -> 4.8 -> 9.1 -> 16 -> 26), i.e. it does NOT converge for this test.

## Honest interpretation (scope)

- The archimedean term Eq.3.7 is a finite, real, ORDER-1 number here
  (+0.294), strictly nonzero because (log(4pi)+gamma)*(f*f)(0) > 0.  This
  concretely confirms the docs/957 ruling: `arch != 0`, no 0-dodge.
- The finite-prime balance is NOT a clean -> 0 complement in either reading:
    * Connes-log convention: finite side ~= +0.00004 (only {2}), so the
      identity gives +0.588 + 0.000043 != 0.
    * valueAt convention: the finite side is not even a finite number here
      (it diverges).
- Therefore the SCAL target `2*arch + (global - restricted) = 0` is NOT a
  structural/definitional identity of this carrier.  Closing it requires the
  real Weil explicit-formula content (a genuine analytic/number-theoretic
  matching of the archimedean and prime-power sums), i.e. the documented open
  analytic bottom.  This probe gives supporting (numerical) evidence, not a
  proof, per the docs/Rel 8xx metrics-wall caveats.

## Clearly not done / not claimed

- No Lean theorem added.  `arch != 0` numerically here; no Lean closure.
- RH is NOT claimed.  Wall-A 1.4 stays OPEN: the arch half is a genuine
  Weil-explicit formula (docs/955/956/957).