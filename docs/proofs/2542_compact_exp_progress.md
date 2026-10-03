Record 2542: compact rational evaluation and adaptive production nodes
Date: 2026-10-04

The computable rational Horner/squaring program now has a Lean proof of
its complex-exponential error bound. All 30 families at the 2541 production
node reproduce the previous exact centers and error radii. The compact
errors also re-establish the signed-node upper 13.7900014901 through the
existing signed sum and coefficient charges. This is a replacement evaluation
proof for an existing node. Four additional production cases now also build,
at indices 5440 and 10239, each with sigma = -1/2 and +1/2. Full-grid and
derivative certificates remain open.

The program rounds coordinates downward at 100 bits and error radii upward
at 140 bits. Its squaring charge retains the current center magnitude and
the squared-error term. The analytic theorem accepts any squaring depth k
provided the scaled complex argument has norm at most one.

The prior bounded external probe checks 77 positions with both endpoint
parameters, totaling 4620 family evaluations. Its maximum depth is 28 and
worst node evaluation charge is 2.9810022494025976e-14 against 1e-8.
Fixed depth six fails the unit-disk gate in 1498 evaluations. This supports
adaptive scaling on the sampled set only; it is not a universal depth bound.

Verification completed in this increment

- C1RouteACompactExp2542 builds after explicit rational-to-real casts and
  normalization of the complex unit and induction arithmetic.
- C1RouteACompactExpReplay2542 builds with decide +kernel. Ordinary decide
  had stopped reducing at rational floor; that failure was not an inequality
  counterexample. The replay proves equality to the prior exact output and
  applies the new analytic theorem to the actual P000 exponential.
- C1RouteACompactExpAudit2542 checks six declarations. Each reports exactly
  propext, Classical.choice, Quot.sound, including the concrete equality.
- C1RouteACompactExpCbv2542 independently proves the same computed equality
  using cbv, with the same three reported axioms.
- The generic module and replay source bytes match the Linux build mirror.

Cost evidence and limits

The replay module reported 45 seconds, the audit-only module 41 seconds,
and the cbv module 41 seconds. The timed cbv Lake invocation took 55.71
seconds wall time, 5.09 seconds user CPU, 5.92 seconds system CPU and
4108916 KiB maximum resident memory. These are whole-process measurements
including dependency loading. They do not isolate arithmetic cost and do
not establish a performance advantage for either tactic.

Next acceptance gates

The matched-import baseline and first 30-family batch both built. Commands
used the resource-aware runner and /usr/bin/time -v around lake build of
C1RouteACompactExpBaseline2542 and C1RouteACompactExpBatch2542 respectively,
in the same WSL workspace. Each module was newly built; dependencies were
already built. These are single observations, not a repeated timing study.

```text
case              wall seconds   user CPU   system CPU   max RSS KiB
----------------  ------------   --------   ----------   -----------
matched imports          54.85       2.87         5.52       3976788
30-family replay         97.56      86.49         8.64       6889924
```

The wall-time difference is 42.71 seconds. The batch includes exact
computation, 30 analytic transfers and 30 axiom reports. Neither the difference
nor its division by 30 is an isolated exponential-evaluation benchmark.
The original batch had line-length warnings; reformatting grows it from
39608 to 41288 bytes without changing its rational data. The comparison
above measures the pre-reformat batch. The prior full-step family files
occupy 618641 bytes; the new shared analytic module is additional to the
batch size. No full-grid cost guarantee follows from this source reduction.

Independent AST parsing matches every input, final center and radius to the
accepted 2541 full-step files and rejects a zeroed output. The new consumer
uses compactNodeError2542, not the old nodeExp_error2541 or old final bound.
The root integration build after reformatting passed. Acceptance checks all
47 audited declarations against the three standard axioms, 733 project source
files byte-for-byte against the build mirror, toolchain/config identity,
regeneration, exact literal readback, and rejection of the corrupted output.
There are no new-module warnings or error lines in the acceptance log.
The final acceptance includes the four adaptive cases below and the project
root build, not only the original-node replay.

Adaptive production cases

The exact position at index 5440 is 65536001/160000000; at index 10239 it
is 335478789119/51200000000. Each module proves its equality to the existing
10240-cell production-grid expression, checks the actual stored squared
widths and signed modulations, and applies the same coefficient midpoints.

```text
index   sigma   active families   max square depth   signed upper
-----   -----   ---------------   ----------------   ----------------------
5440    -1/2                 30                  6   766536121/2000000000
5440    +1/2                 30                  6   721605217/1250000000
10239   -1/2                  1                 17   1/5000000000
10239   +1/2                  1                 17   1/5000000000
```

These are certified order-zero signed center-plus-error bounds. Applying
them to the intended exact interpolation coefficients still requires their
membership in the imported boxes. Each proof retains the final complex sum
before the norm, charges evaluation error by 1e-12, and coefficient error
by 30e-30. The reported upper includes both charges.

At index 10239 the 29 exterior families vanish by their actual piecewise
definitions. The remaining family uses a 17-square calculation and retains
a positive error radius even when its computed center is zero. No floating
underflow argument establishes a zero function value.

Independent arithmetic parsing reconstructs each scaled exponent from the
capture, checks the unit-disk condition, replays all rounded Horner/square
steps, checks the final center/radius, and reconstructs the signed sum.
Zeroing an active output is rejected in each of the four cases. This reader
does not use the adaptive evaluator to calculate the expected output.

Next steps

1. Add derivative certificates and segmented grid sums before treating this
   representation as a full-grid proof mechanism.
2. Prove exact-coefficient membership for the original interpolation problem.
   Imported boxes alone do not establish that the intended coefficients lie
   in them.
3. Retain correction-channel
   obligations when transferring the eventual grid result to the selected owner.

Exact interpolation-owner membership, full-grid integration, correction
channels, selected-owner positivity and RH remain open.

Evidence:
ConnesWeilRH/Dev/C1RouteACompactExp2542.lean
ConnesWeilRH/Dev/C1RouteACompactExpReplay2542.lean
ConnesWeilRH/Dev/C1RouteACompactExpAudit2542.lean
ConnesWeilRH/Dev/C1RouteACompactExpCbv2542.lean
results/2542_exp_schedule_probe.json
ConnesWeilRH/Dev/C1RouteACompactExpBatch2542.lean
ConnesWeilRH/Dev/C1RouteACompactNode2542.lean
scripts/validate_compact_replay_2542.py
results/2542_compact_replay_readback.json
scripts/generate_adaptive_nodes_2542.py
scripts/validate_adaptive_nodes_2542.py
results/2542_adaptive_node_readback.json
