# 074 Canonical Xi-Quotient Candidate

Date: 2026-07-12

Result: one new detector construction survives the initial conceptual screen
and merits a rejection-first plan. It has not yet passed its analytic or
consumer gates.

## Idea

Given a hypothetical off-line zero `rho`, divide the completed Xi function by
the polynomial carrying the full functional-equation/conjugation orbit of
`rho`, with exact analytic multiplicities. The quotient is intended to retain
zeros at every other source zero while becoming nonzero on the removed orbit.
A finite polynomial chooses a negative orbit value pattern.

The inverse transform is noncompact. Instead of interpolating an expanding
finite list of zeros, cut this one exact detector in physical space and prove
that its transform error is summable over every source zero.

```text
Xi quotient
  -> exact zero at every non-target source zero
  -> one physical-tail error after cutoff
  -> zero-counting theorem sums that error
```

This removes the logical shape that killed Plan 023:

```text
nearby radius -> correction constants -> later threshold -> failed fixed point.
```

## Evidence

The project already proves that `completedRiemannXi` is entire, nonzero at
`2`, satisfies `Xi(1-s)=Xi(s)`, has finite analytic order at every point, and
vanishes at every source nontrivial zero. It also exposes a Mellin kernel with
explicit small/large interval exponential bounds and source-zero summability
consumers.

Burnol's direct proof of the converse Weil criterion confirms the relevant
proof architecture: construct the negative zero direction in a larger test
class, then return to smooth compact support. Source:
<https://arxiv.org/abs/math/9810169>, pp. 4-5.

The two newest operator candidates do not supply a competing completed
producer. Suzuki's RH-facing statement is the conditional limit in Corollary
1.6 of <https://arxiv.org/abs/2606.09096>. The Volterra/Weyl paper
<https://arxiv.org/abs/2606.29555> explicitly leaves the quotient lift,
uniform parameter coverage, and final de Branges/RH bridge open.

## Primary Risks

```text
division may leave a non-admissible exponential physical tail
conjugation symmetry and multiplicities may not transport on one owner
compact cutoff convergence may be pointwise but not summable over zeros
the finite orbit square may have the wrong Hermitian sign
the detector may still have no lower source-sign consumer
```

## Verdict

```text
conceptual novelty relative to Plan 023: yes
uses existing Xi/counting infrastructure: yes
analytic construction: unproved
lower consumer: unproved
Lean work authorized: no
next gate: one-factor division and inverse-transform tail
```

The execution contract is
`plan/025_2026-07-12_canonical_xi_quotient_detector_plan.md`.
