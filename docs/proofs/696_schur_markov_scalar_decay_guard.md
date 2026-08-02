# Proof 696: Schur-Markov scalar decay guard

Date: 2026-07-31

Status: exact obstruction guard. This proof does not close Gate 3U.

## Result

For the legal visible-prime sequence

```text
p_n = (n + 2)^2
```

Lean proves

```text
primeSchurMarkovScalar p_n = (n + 1) / (n + 3)
rho_N = 2 / ((N + 1) * (N + 2))
```

for the literal prefix `p_0, ..., p_(N-1)`. Consequently, for every
positive `epsilon`, some finite suffix has `rho_N < epsilon`.

The exact source declarations are:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSchurMarkovScalarDecayGuard.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSchurMarkovScalarDecayGuardAudit.lean
```

## Consequence

The existing Schur-Markov theorem controls a scalar-weighted absolute response.
Because the scalar has no positive lower bound on literal suffixes, one cannot
obtain Gate 3U by dividing that estimate by `rho_S`.

This is not a counterexample to the actual signed physical estimate. It only
rules out a normalization shortcut. The required producer remains a bound on
the complete signed object before the first absolute value, with a constant
independent of the finite prime set.

The active quantitative target is still

```text
abs Tr_B(
  mathcalD_S *
    (C_0[W,E]B - [W,R]R L_S)
)
  <= C * (1 + B_root)^d * ||g||_(H^r)^2
```

or its equivalent antiresonant alternating-primitive bound over all
route-valid `(p, S, N)`. Existing terminal decay and compactness only give
strong convergence for each fixed step; they do not give the needed uniform
bound.

## Verification

The Windows repository was verified in an Ubuntu-24.04 WSL2 ext4 mirror under
the shared Lake lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 696 source                     | 3333  | PASS   |
| Proof 696 audit                      | 3334  | PASS   |
| CCM25Concrete aggregate              | 3971  | PASS   |
| full repository                      | 4052  | PASS   |
+--------------------------------------+-------+--------+
```

The audited declarations use exactly `[propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, user axiom, heartbeat increase, or recursion-limit
increase was added.
