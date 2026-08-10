# 965 - Wall-A 1.4 kill verdict (healthy carrier)

Date: 2026-08-10.  Status: consolidated decision on Wall-A 1.4 after full
algebraic reduction + refutation hinge + explicit self-created witness, all
axiom-clean and pushed.  RH NOT claimed.

## The whole Wall-A 1.4 now reduces to ONE scalar

On the healthy carrier (`ScabLhsZero.healthySymbols`, per-common finite-prime
set `{2}`), for `lambda >= sqrt 2` the global and restricted finite-prime sums
are equal, so (docs/956/963/964):

```text
healthy SCAL/SCB  <->  arch(f*f) = 0
```

with the refutation hinge `arch(f*f) != 0 -> Not (healthy target)` and the
explicit self-created witness `witnessTest = unitFourierCoreBumpSchwartz`
(`Wall14ArchReduction.lean`, `Wall14SelfTestWitness.lean`).

## What is closed (axiom-clean, pushed)

- `healthy_scb_arch_zero_of_global_eq_restricted`: healthy SCAL/SCB <-> `arch=0`.
- `healthy_target_refuted_of_arch_ne_zero`: `arch != 0 -> Not(healthy target)`.
- `Wall14SelfTestWitness`: refutation pinned to an explicit, computable test
  (`test(0) = 1`, nonzero).  The healthy claim must hold for ALL tests, so a
  single test with `arch != 0` suffices to refute it.
- `witnessTest_ne_zero`, smooth/even/compact.

## What remains (= the only surviving step)

Prove `arch(f*f) != 0` for the explicit witness, i.e. the real Eq.3.7
archimedean integral

```text
arch = (log(4*pi)+gamma)*Re((f*f)(0)) + I
        |___________>0_________|     |_ I = Int_{y>0} (e^(y/2)(g+gi) -2g(0))/(e^y-e^-y) dy _|
```

- Leading term: `Re((f*f)(0)) = norm^2 L2 > 0` (via
  `convolutionSquare_zero_eq_integral_normSq`), and `log(4*pi)+gamma > 0`.
- `the integral` `I` is the decisive, currently-not-lean-closed part.

## Why this is an honest dead verdict for the route

- On the healthy carrier, Wall-A 1.4 as a *positive theorem* fails: docs/958
  probes `arch = +0.294 != 0` on the route proxy, so `2*arch + (global-restricted)`
  is non-zero and the SCB is refuted.
- Every Lean-assemblable layer of the wall is now closed and pinned to a single
  scalar at a concrete test.  The single residual (the archimedean integral) is
  the same operator<->scalar seam as the RH-equivalent C1 criterion (docs/963);
  closing it needs genuinely new analysis, not an assembly leaf.

## Wall-A 1.4 verdict

`healthy-carrier Wall-A 1.4 is dead as a provable identity`: the balance reduces
to `arch = 0` on that carrier, the evidence refutes `arch = 0`, and no Lean
formulation can force it without the Eq.3.7 integral control. The route must
re-point; the residual analytic is documented separately (docs/966 plan).
RH not claimed.

## Cross refs

docs/952, 954, 955, 956, 957, 958, 963, 964; `Dev/Wall14ArchReduction.lean`,
`Dev/Wall14SelfTestWitness.lean`, `Dev/ScabLhsZero.lean`.