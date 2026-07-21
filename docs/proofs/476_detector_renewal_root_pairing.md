# Proof 476: Detector renewal root pairing

## Result

The result is good for trace/renewal legality, but it does not close Gate 3U
or RH. Proof 476 keeps the complete finite-Euler operator intact while fixing
the order in which its basis trace and causal renewal series are evaluated.

Write

```text
B   = source quotient-band projection,
R   = source Sonin projection,
C   = selected compact convolution root,
W   = C^dagger C,
A_S = normalized finite-Euler inverse.
```

Proof 475 handled one displacement. The new finite-S factorization is

```text
completeCorner_S
  = B[W,R] R A_S B
  = (C B)^dagger (C R A_S B).
```

The right side is formed before renewal expansion: `C R A_S B` is one bounded
right root leg. The complete physical three-branch Hilbert--Schmidt pair,
sandwiched by `B` and `R A_S B`, proves
`IsTraceClassAlong` for this whole operator.

For each fixed input vector `u`, Lean then applies the existing vector-level
probability law

```text
A_S(Bu)
  = sum'_omega weight_omega U_(-z_omega)(Bu)
```

through the bounded map `C R`. For fixed vectors `x,y`, applying the continuous
inner-product functional gives the summable scalar series

```text
<C B x,C R A_S B y>
  = sum'_omega weight_omega
      <C B x,C R U_(-z_omega) B y>.
```

The two legality arguments have different owners:

```text
+---------------- complete physical pair ----------------+
|                                                        |
|  B[W,R] R A_S B  ---->  sum'_i diagonal_i             |
|        |                         |                     |
|        | factor                  | fix i               |
|        v                         v                     |
|  (C B)^dagger(C R A_S B)   sum'_omega weightedPair    |
|                                                        |
+--------------------------------------------------------+
```

Consequently the ordinary trace has the exact ordered form

```text
sum'_i sum'_omega weight_omega
  <C B e_i,C R U_(-z_omega) B e_i>.
```

The inner renewal series is summable for every fixed `i`; the outer series of
the already averaged diagonals is summable because the complete operator is
`IsTraceClassAlong`.

## Verification

The Windows source was copied one way into the Ubuntu 24.04 ext4 verification
mirror. The acceptance batch passed:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 476 source plus focused audit                  |  3272 | PASS   |
| CCM25Concrete aggregate                              |  3751 | PASS   |
| full repository                                      |  3832 | PASS   |
+------------------------------------------------------+-------+--------+
```

All ten audited theorems depend exactly on

```text
[propext, Classical.choice, Quot.sound]
```

The Proof 476 source and audit contain no `sorry`, `admit`, or new `axiom`.
The build emitted only existing repository linter warnings and the local WSL
proxy notice; the new Proof 476 module emitted no linter warning.

## Boundary

Proof 476 does not exchange the two `tsum`s. In particular, it does not prove

```text
sum'_i sum'_omega pairing(i,omega)
  = sum'_omega sum'_i pairing(i,omega),
```

and it does not identify the trace with a sum of atomwise traces. Separate
Hilbert--Schmidt estimates for `C B` and `C R U_(-z)B` remain forbidden by
Proof 259's infinite-mass obstruction. Large displacement alone also does not
make the root pairing vanish because `R` is not translation invariant.

The next analytic producer must bound the displayed correctly ordered scalar
uniformly in the visible finite prime set, using compact-root relative-support
geometry before any absolute value. Gate 3U, the finite-S sign,
negative-owner integration, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.
