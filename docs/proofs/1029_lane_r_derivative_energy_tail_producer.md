# 1029 - Derivative-energy Gamma_R tail producer

Date: 2026-08-19.

## Verdict

The Gamma_R shifted-tail route now has an unconditional derivative-energy
producer for every compact-log test.  It replaces the rejected assumption
that a convolution-square Lipschitz constant can be controlled by square mass
alone.

The producer is magnitude-only.  It proves an explicit absolute tail rate;
it does not prove a tail sign, the finite constrained-prefix inequality,
global spectral nonnegativity, or RH.

The dependency is:

```text
compact-log derivative energy E(g) = integral ||g'(t)||^2 dt
                              |
                              v
convolution-square derivative bound
  ||(g^* * g)'(x)|| <= sqrt(squareMass(g)) * sqrt(E(g))
                              |
                              v
support-local Lipschitz certificate for g^* * g
                              |
                              v
explicit Gamma_R shifted-tail norm rate
```

## Lean owner

`Dev/C1XiCenterTwoGammaDerivativeEnergy.lean` defines
`compactLogDerivativeEnergy` and
`convolutionSquareDerivativeEnergyCoefficient`:

```text
E(g) = integral t, ||deriv g.test t|| ^ 2
A(g) = sqrt((g^* * g)(0).re) * sqrt(E(g)).
```

`norm_deriv_convolutionSquare_le_derivativeEnergyCoefficient` proves

```text
||deriv (g^* * g).test x|| <= A(g)
```

The proof reads the derivative of the genuine convolution, applies the
Holder-conjugate `L2` integral inequality, and transports the derivative
energy through reflection and translation.  The support-local Lipschitz
theorem then supplies the exact certificate expected by
`gammaRArchProfileTerm_norm_le_of_support_lipschitz`.

The public tail theorem is
`gammaRArchProfileTailNorm_le_derivativeEnergy_rate`.  Its profile constant
is

```text
2 * A(g) + (g^* * g)(0).re
```

and it feeds the existing `gammaRArchProfileTailExplicitRate` for every
`N > 0`.

## Verification

WSL2 ext4 verification used the shared Lean lock:

```text
lake build ConnesWeilRH.Dev.C1XiCenterTwoGammaDerivativeEnergy
lake build ConnesWeilRH.Dev.C1XiCenterTwoGammaDerivativeEnergyProbe
```

The owner completed at `3542` jobs and the import-facing probe at `3543`
jobs.  The probe audits the six public declarations introduced by the owner;
each reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, project axiom, RH root axiom, or numerical-to-Lean
transfer in this producer.

## Boundary and next target

The derivative-energy coefficient is explicit but still depends on the test's
derivative energy.  It is therefore not a frequency-uniform mass-only bound,
which is consistent with the 1027 stress screen.  The remaining substantive
Gamma_R task is the finite constrained-prefix inequality, or a coupled
quadratic estimate that can consume this tail bound.  Until that producer is
closed, the universal Lane R inequality and unconditional RH remain open.
