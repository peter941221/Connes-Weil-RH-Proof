# Proof 1243 — G8 finite-window trace carrier

Status: FORMAL-ALGEBRA (Lean), 2026-09-10.

The existing finite-window Hilbert--Schmidt factor is inserted on both sides
of the G8 ambient Gram kernel:

```text
C_{g,n}† · G8(owner, λ, family) · C_{g,n}.
```

Here `C_{g,n}` is the existing `fullBoundaryPositiveOperator` at the
test-owned cutoff, and `G8` is the adjoint-shear Gram operator from record
1242.  The concrete owner is `g8CutoffPairData` in
`ConnesWeilRH.Dev.C1G8AdjointShearGram`.

Lean proves, on the same whole-line carrier and caller-supplied basis:

1. the trace product is exactly the displayed sandwich;
2. it is trace-class by the existing Hilbert--Schmidt column-sum certificate;
3. it is positive by `IsPositive.adjoint_conj`; and
4. its ordinary trace has nonnegative real part.

Audit evidence: `/home/peter/rh/build-logs/1243_g8_cutoff_retry2.log`.
The log has `Build completed successfully (3921 jobs)`, no `error:` or
`sorryAx`, and the paired audit prints only
`[propext, Classical.choice, Quot.sound]` for all five new declarations.

This does not identify the finite-window trace with `qw`, prove a cutoff
limit, or prove the finite visible-prime sign.  Those remain the live G8
consumer obligations; no interface-level positivity is being counted as an
RH step.
