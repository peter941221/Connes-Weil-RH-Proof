# 2448 - Route A interval algebra and direct consumer acceptance

Date: 2026-10-02.

The interval algebra prerequisite recorded as failing in 2447 now passes in
the WSL ext4 build mirror. The repair preserves the interval definitions and
theorem statements. It also restores the direct owner and phase consumers;
it does not import numerical endpoint certificates.

## Failure mechanism and repair

`Set.uIcc left right` includes all values between its two endpoints, regardless
of their order. For example, multiplying the interval [2,4] by -3 reverses
the endpoints to -6 and -12. Its minimum is -12, not -6.

The former proof applied `Set.mem_uIcc`, which returns a disjunction of the
two endpoint orders, as if it supplied fixed lower and upper inequalities.
The repaired real multiplication proof uses the underlying membership fields
directly: the first bounds the minimum and the second bounds the maximum.
It then splits on the sign of the multiplier and links those bounds to the
four-corner minimum/maximum hull.

Additional repairs within the same direct dependency chain:

- Complex multiplication now builds each real/imaginary interval membership
  from both inequalities, rather than supplying one inequality as a pair.
- `Mathlib.Data.Complex.BigOperators` supplies finite-sum real/imaginary
  readback. `Complex.SMul` enables the existing real scalar action, retaining
  the statement of `mem_scale` without an API change.
- The owner term consumer now directly imports `C1RouteAMPFRInterface` and
  opens the namespace containing `storedWidth` and `correctedPhysical`.
- The phase consumer directly imports `Mathlib.Analysis.Complex.Trigonometric`
  and uses the real/imaginary exponential identities. The broad phase box is
  obtained from the same narrow-interface theorem and the global sine/cosine
  bounds; no endpoint hypotheses are removed.

Six exact Lean regression examples cover negative times positive intervals,
mixed-sign intervals, zero intervals, point intervals, the four-corner hull,
and reversed-endpoint subtraction. The audit now also prints axioms for
`mem_sumFinset`, real addition, and real subtraction.

## Acceptance evidence

The final resource-managed WSL build uses Lean v4.30.0 in the Linux-side
verification environment. From its repository root, the equivalent command is:

    bash scripts/run_resource_aware_task.sh --workspace "$PWD" \
      --log "$PWD/build-logs/2448_route_batch_final.log" -- \
      lake build \
      ConnesWeilRH.Dev.C1RouteAIntervalAlgebraAudit \
      ConnesWeilRH.Dev.C1RouteAMPFRInterfaceAudit \
      ConnesWeilRH.Dev.C1RouteAOwnerTermInterfaceAudit \
      ConnesWeilRH.Dev.C1RouteAPhaseBoundsAudit \
      ConnesWeilRH.Dev.C1RouteAPhaseBoundsNarrowAudit

The final log contains:

    Build completed successfully (3716 jobs).

There are zero lines beginning `error:`. All 22 printed declarations have
exactly `[propext, Classical.choice, Quot.sound]`. Nine direct-chain source
files match byte-for-byte between Windows and the Linux mirror. The changed
Lean sources contain no `sorry`, `admit`, or added axiom declarations.

Evidence:

- `build-logs/2448_route_batch_final.log`
- `results/2448_routea_interval_algebra_validation.json`
- `ConnesWeilRH/Dev/C1RouteAIntervalAlgebra.lean`
- `ConnesWeilRH/Dev/C1RouteAIntervalAlgebraAudit.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerTermInterface.lean`
- `ConnesWeilRH/Dev/C1RouteAPhaseBounds.lean`

The earlier integration failures remain in
`build-logs/2448_interval_audits.log` and
`build-logs/2448_phase_integration.log`. They identify the owner namespace,
directed-value import, and trigonometric import failures corrected above.
The first attempt in this round mistakenly used the `/mnt/c` tree and was
cancelled; it is not acceptance evidence. An initial mirror attempt also
lacked the audit source files. Only the final ext4 build is accepted here.
The final build replays existing warnings in unchanged dependency modules;
none is suppressed. This is not a full project-root aggregate build.

## Mathematical boundary and next obligation

The accepted chain is:

```text
certified real endpoints
          |
          v
real interval operations
          |
          v
complex rectangle operations
          |
          v
directed family product / finite sum
          |
          v
same-owner correctedPhysical containment
```

The first line still needs actual endpoint proofs. The 2445 independent
point-box replay and 2446 evaluator smoke are external numerical controls,
not Lean proofs of those inequalities. No continuum enclosure, quadrature
error, selected-detector signed budget, producer GO, or RH claim is made.

The next step is to align the 2445 stored inputs and support-branch decisions
with the exact owner definitions before attempting numeric Lean import.
Once actual factor endpoint inequalities are proved, the now-building
2437/2436 consumers can assemble them without replacing the selected owner.
The later integral and signed-budget obligations remain separate.
