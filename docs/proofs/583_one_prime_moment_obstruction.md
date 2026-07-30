# Proof 583: one-prime moment obstruction

## Result

Define the actual empty-suffix old-carrier analysis and the first nontrivial
boundary moment by

```text
W_p y = ( ambientLossFactor_p^dagger y,
          (I - newFrame_0 newFrame_0^dagger) T_p^dagger y )

M_p = rawCoframeBoundaryMoment
       (forward_[p], endpoint_[p]).
```

Proof 581 gives the exact row cancellation

```text
R_0(p, []) = -T_p^dagger M_p oldFrame_p^dagger.
```

If a uniform old-carrier Douglas quotient `R_0 = Q_p W_p` exists with bound
`C`, the reverse Schur--Markov transition cancels `T_p^dagger` and produces a
moment readout.  Because `rho_p >= 1/8`, its norm is at most `8 C`:

```text
M_p oldFrame_p^dagger = Q'_p W_p,
||Q'_p|| <= 8 C.
```

The Lean theorem
`onePrimeBoundaryMoment_oldCarrier_norm_le` proves the corresponding
pointwise estimate on the actual global-log carrier.  Consequently,
`noExistsUniformOldCarrierDomination_of_onePrimeMomentApproximateKernel`
proves:

```text
||W_(p_n) y_n|| -> 0
and
||M_(p_n) oldFrame_(p_n)^dagger y_n|| >= epsilon eventually
    ==> no finite uniform old-carrier Douglas bound.
```

## Why this is a new bone-1 target

The previous approximate-kernel guard used the raw four-term row directly.
This batch moves the test to the exact one-prime boundary moment on the same
old-carrier analysis.  It removes the transition factor from the obstruction
and isolates the remaining source question to one explicit signed operator.

```text
 +----------------------------+
 | actual old-carrier W_p     |
 +-------------+--------------+
               |
               v
 +----------------------------+
 | one-prime moment M_p       |
 | M_p oldFrame_p^dagger      |
 +-------------+--------------+
               |
               v
 +----------------------------+
 | approximate kernel test    |
 | W_p y_n -> 0, M_p y_n !->0|
 +-------------+--------------+
               |
               v
 | uniform Douglas quotient   |
 | is impossible              |
 +----------------------------+
```

This is still an obstruction theorem, not a constructed sequence.  No actual
moment approximate kernel, uniform old-carrier quotient, Gate 3U estimate,
finite-S sign, Burnol identity, or RH proof is claimed.

## Lean owners

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstructionAudit.lean
```
