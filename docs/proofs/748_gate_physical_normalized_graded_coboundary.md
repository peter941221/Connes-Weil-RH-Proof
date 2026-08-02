# Proof 748: Gate Physical Normalized Graded Coboundary

## Result

The result is structurally positive but does not close Gate 3U.  Proof 748
splits Proof 747's ordered normalized double boundary into its symmetric
graded semicommutator and the exact Gram-similarity anomaly.  The split is an
operator identity; the two resulting terms are not assigned separate trace
bounds.

```text
+--------------------------------------+----------------------------------+
| layer                                | result                           |
+--------------------------------------+----------------------------------+
| normalized inverse Gram             | contraction, inherited from 747  |
| left/right boundary numerators       | exact adjoint pair               |
| numerator asymmetry                  | exact Gram coboundary             |
| symmetric numerator                  | self-adjoint                     |
| ordered similarity anomaly          | exact, not known to vanish        |
| complete target                      | symmetric term plus anomaly       |
| Gate 3U / finite-S sign / RH         | open                             |
+--------------------------------------+----------------------------------+
```

## 1. What It Is

Write

```text
J     = sourceInclusion,
W     = detectorOperator,
G_S   = J^dagger H_S J,
H_S   = T_S^dagger T_S,
X     = J^dagger W J,
c_S   = finiteEulerLowerFactor(S),
Ghat  = c_S^(-2) G_S,
Ahat  = c_S^2 G_S^(-1).
```

Let `K_S` denote the transported-frame detector compression

```text
K_S=(T_S J)^dagger W(T_S J).
```

Proof 748 defines the normalized left and right boundary numerators

```text
Lhat_S=c_S^(-2)(K_S-G_S X),
Rhat_S=c_S^(-2)(K_S-X G_S).                         (GC.1)
```

The left numerator is the ordered double boundary from Proof 747:

```text
Lhat_S
 =J^dagger(c_S^(-2)[R,H_S])[W,R]J.                 (GC.2)
```

The target is therefore

```text
Target_S=Ahat Lhat_S.                               (GC.3)
```

## 2. Why It Is Needed

Proof 332 identified the symmetric graded semicommutator as the correct
support-first two-point object.  Proof 747, however, retained one ordered
Gram response.  In infinite dimension those are not automatically the same
trace: cycling a bounded similarity can leave a nonzero boundary anomaly.

The missing relation is now exact:

```text
Lhat_S-Rhat_S=X Ghat-Ghat X.                        (GC.4)
```

Thus the asymmetry is neither an uncontrolled remainder nor zero.  It is one
named source detector/Gram coboundary.  Equation `(GC.4)` is proved before
any trace is taken, so it does not use the invalid rule
`Tr(AB)=Tr(BA)` for two merely bounded factors.

The structural picture is

```text
                  +------------------------------+
                  | ordered target Ahat Lhat_S   |
                  +---------------+--------------+
                                  |
                   exact half-sum | exact half-difference
                                  v
       +--------------------------+--------------------------+
       |                                                     |
+------v----------------------+          +-------------------v------+
| symmetric graded           |          | Gram-similarity anomaly  |
| semicommutator              |          |                          |
| Ahat (Lhat+Rhat)/2          |          | (Ahat X Ghat-X)/2        |
+-----------------------------+          +--------------------------+
       |                                                     |
       +--------------------------+--------------------------+
                                  |
                                  v
                   keep one signed scalar until
                   compact-root support has acted
```

## 3. Exact Decomposition

Define

```text
Sym_S=(Lhat_S+Rhat_S)/2,
Anom_S=(Ahat X Ghat-X)/2.                            (GC.5)
```

Lean proves

```text
Rhat_S=Lhat_S^dagger,
Sym_S=Sym_S^dagger,

Anom_S=Ahat(Lhat_S-Rhat_S)/2,

Target_S=Ahat Sym_S+Anom_S.                         (GC.6)
```

The last line is named
`finiteEulerNormalizedGradedCoboundaryResponse`.  The route-facing theorem
proves that family-uniform boundedness of the existing lower-factor-gauged
Gate trace is equivalent to family-uniform boundedness of the ordinary trace
of this complete response.

No additivity theorem is used to split that ordinary trace into two traces.
In particular, Proof 748 does not assert trace legality or a bound for either
summand in isolation.

## 4. Relation To Support-First Analysis

Both boundary commutators in `(GC.2)` are skew-adjoint.  Averaging the left
order with its adjoint produces the anticommutator orientation needed by the
symmetric two-point covariance of Proofs 301 and 332.  The inverse Gram
factor remains on the left and is the contraction proved in Proof 747.

The second term in `(GC.6)` records exactly what a finite-dimensional trace
cycle would erase.  Therefore the legal analytic order is

```text
normalized inverse Gram
  -> symmetric boundary plus ordered similarity anomaly
  -> complete outer/second-support/prolate expansion
  -> compact-root support
  -> one scalar absolute value.                       (GC.7)
```

The following shortcut remains forbidden:

```text
estimate only Ahat Sym_S
  -> discard Anom_S as a commutator trace
  -> claim Gate 3U.                                   (GC.8)
```

An infinite-dimensional commutator trace need not vanish under the current
diagonal-series legality.  A source-specific producer must either cancel
`Anom_S` inside the complete physical scalar or estimate the sum in `(GC.6)`
without separating it.

## 5. Lean Ownership

The source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalNormalizedGradedCoboundary.lean
```

The import-facing audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalNormalizedGradedCoboundaryAudit.lean
```

The accepted WSL2 builds were

```text
+----------------------------------+-------+--------+
| target                           | jobs  | result |
+----------------------------------+-------+--------+
| focused source + axiom audit     |  3392 | PASS   |
| CCM25Concrete aggregate + audit  |  4017 | PASS   |
| full repository                  |  4097 | PASS   |
+----------------------------------+-------+--------+
```

All sixteen audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`.

## 6. Remaining Bottom

Proof 748 does not prove that `Anom_S` vanishes, and it does not give a
uniform estimate for `Ahat Sym_S+Anom_S`.  The next producer must use the
actual real-line compact-support geometry and the complete
outer/second-support/prolate owner to establish a uniform signed scalar bound
before the first absolute value.

Gate 3U, the finite-S sign, the arithmetic same-object identity, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
