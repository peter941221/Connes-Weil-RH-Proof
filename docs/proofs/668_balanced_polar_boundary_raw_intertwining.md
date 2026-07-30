# Proof 668: balanced polar-boundary raw intertwinement

## Result

The algebraic result is good, but the analytic conclusion is negative:
Proof 667's residual is **exactly** the already known raw quadratic
intertwinement (raw quadratic intertwinement), up to its required scalar and
orientation. The polar-gauge route has therefore isolated the Bone 1A
survivor cleanly, but it has not created a new estimate for it.

Write

```text
Raw_S = complete raw quadratic response,
Q_S   = balanced raw quadratic response,
R_S   = G_S^(-1/2),
L_S   = R_S G_S,
H_(p,S)=L_(p::S)R_S,
D_S   = U_S^dagger W U_S,
E_S   = B_0-F_S.
```

The endpoint gauges obey

```text
R_S L_S=I,
L_S R_S=I.
```

## Same-suffix collapse

Proof 665 already gives

```text
Raw_S=F_S+(A_S G_S^(-1)-B_0),
A_S=L_S D_S L_S,
G_S^(-1)L_S=R_S.
```

Substitution into `Q_S=R_S Raw_S L_S` yields

```text
Q_S
  =D_S-R_S(B_0-F_S)L_S
  =D_S-R_S E_S L_S.
```

This is the common producer that Proof 667's two residual terms were hiding.
The proof uses a generic noncommutative-ring identity (noncommutative-ring
identity) and the three displayed inverse relations; it does not unfold the
continuous functional calculus (continuous functional calculus, CFC) square
root.

```text
 +----------------------+       +----------------------+
 | metric increment     |       | base/first-jet term  |
 | D_new-D_old          |       | R E L                |
 +----------+-----------+       +-----------+----------+
            |                               |
            +---------------+---------------+
                            v
                 Q_S=D_S-R_S E_S L_S
                            |
                            v
                    Q_new-Q_old
```

## Adjacent gauge cancellation

Proof 667's survivor is

```text
Residual_(p,S)
  =H_(p,S)E_S-E_(p::S)H_(p,S)
    +L_(p::S)(D_(p::S)-D_S)R_S.
```

Using the same-suffix identity before any norm gives

```text
Residual_(p,S)
  =L_(p::S)(Q_(p::S)-Q_S)R_S.
```

Now substitute `Q_S=R_S Raw_S L_S`. Both endpoint gauges cancel:

```text
Residual_(p,S)
  =Raw_(p::S)H_(p,S)-H_(p,S)Raw_S.
```

Because `H_(p,S)=(1+q_p)T_(p,S)`, this is precisely

```text
Residual_(p,S)
  =-(1+q_p)
     [T_(p,S)Raw_S-Raw_(p::S)T_(p,S)]

  =-(1+q_p) RawIntertwiningDefect_(p,S).
```

The sign and transition orientation are part of the theorem. Reversing them
would reconnect the wrong row.

## Route scaling

Proof 667 established the exact scalar identity

```text
q_p^(-1/2)(1+q_p)=s_p^(-1),
```

where `s_p` is the ambient-loss scale. Therefore Lean proves the operator
equality

```text
RouteScaledResidual_(p,S)
  =-RouteScaledRawIntertwiningDefect_(p,S).
```

In particular,

```text
||RouteScaledResidual_(p,S)||
  =||RouteScaledRawIntertwiningDefect_(p,S)||.
```

The route-uniform bound predicates are equivalent with the **same** constant.
Combining this with Proof 667 gives the exact recurrence split

```text
RouteScaledPolarFirstJetRecurrence
  =RouteScaledControlledPolarBoundary
    -RouteScaledRawIntertwiningDefect,
```

and closes the algebraic loop

```text
Bone 1A route-uniform bound exists
  <->
route-uniform ambient-loss-scaled raw-intertwinement bound exists.
```

## Consequence

This proof is a route guard. Repackaging the Proof 667 residual through more
balanced gauges cannot produce a new bound: Lean has identified the residual
with the original raw defect as an operator. The next producer must act on
that raw defect using source-specific real-line geometry, its completed
physical factorization, or a genuinely new cancellation theorem. Estimating
the base/first-jet covariance and detector metric increment separately remains
invalid.

Proof 656's route-uniform two-step factor is still a separate Bone 1
requirement. Gate 3U, the finite-S sign, Burnol's identity, and RH remain
open.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorBalancedPolarBoundaryRawIntertwining.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorBalancedPolarBoundaryRawIntertwiningAudit.lean
```

## Verification

The Windows truth source was copied to the Ubuntu-24.04 WSL2 ext4 mirror and
built under the shared Lake lock.

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 668 focused source + audit     |  3456 | PASS   |
| CCM25Concrete aggregate              |  3943 | PASS   |
| full repository                      |  4024 | PASS   |
+--------------------------------------+-------+--------+
```

All nine audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, user axiom,
heartbeat increase, or new source linter warning was added.
