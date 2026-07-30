# Proof 630: single-channel renewal deviation

## Result

Proof 630 rewrites the complete Proof 628 denominator as one normalized
renewal deviation.  With

```text
q_p   = ccm24PrimeEulerCoefficient(p),
rho_p = primeSchurMarkovScalar(p),
L_p   = primeEulerAmbientLossFactor(p),
N_p   = normalizedPrimeEulerInverse(p),
```

Lean proves the ambient operator identity

```text
N_p^dagger - rho_p I
  = sqrt(q_p) L_p^dagger N_p^dagger.
```

The order remains `L_p^dagger N_p^dagger`; no commutation is used.  After
attaching the actual new suffix frame, define

```text
D_(p,S) = (N_p^dagger - rho_p I) newFrame_(p,S),
B_(p,S) = L_p^dagger N_p^dagger newFrame_(p,S).
```

Then

```text
D_(p,S) = sqrt(q_p) B_(p,S),
||D_(p,S)x||^2 = q_p ||B_(p,S)x||^2.
```

## Derivation

The proof uses the same two exact Euler identities as Proof 629:

```text
U_p^dagger - I = -sqrt(q_p) L_p^dagger,
U_p^dagger N_p^dagger = rho_p I.
```

Postcomposing the first identity by `N_p^dagger` and substituting the second
gives

```text
rho_p I - N_p^dagger
  = -sqrt(q_p) L_p^dagger N_p^dagger.
```

Negating both sides produces the displayed renewal-deviation formula.

```text
 +---------------------------+
 | (U^dagger - I) N^dagger   |
 +-------------+-------------+
               |
       +-------+--------+
       |                |
       v                v
 +-----------+   +-------------------+
 | rho I-N^d |   | -sqrt(q) L^d N^d |
 +-----+-----+   +---------+---------+
       |                   |
       +---------+---------+
                 v
 +-----------------------------------+
 | N^dagger-rho I=sqrt(q)L^daggerN^d |
 +-----------------------------------+
```

## Equivalent Bone 1 target

The route-uniform relative-energy domination from Proof 628 is equivalent,
with exactly the same bound `C`, to

```text
q_p ||signedCompressedInteriorOwner_(p,S) x||^2
  <= C^2 ||D_(p,S) x||^2
```

for every route-valid `(p,S)` and source vector `x`.

This is useful because both sides now expose a `rho_p`-difference: the
numerator is uniformly equivalent, up to the fixed factor `8`, to the
reverse-intertwining defect

```text
R_(p,S)^dagger B_S - B_(p::S) R_(p,S)^dagger,
```

while the denominator is the ambient renewal deviation
`N_p^dagger-rho_p I`.  A future source estimate can compare these two
same-step differences directly.

## Boundary

Proof 630 is an exact normal form and same-bound equivalence.  It does not
bound the reverse-intertwining defect by the renewal deviation.  The source
contains no theorem making the defect zero, and route validity contributes
only `(p :: S).Nodup`, not analytic covariance.

The active theorem is therefore still

```text
exists C >= 0, forall route-valid (p,S), forall x,
  q_p ||K_(p,S)x||^2 <= C^2 ||D_(p,S)x||^2,
```

up to the already proved universal factor `8` between `K_(p,S)` and the
signed interior owner.  Bone 1, Gate 3U, the finite-S sign, Burnol's identity,
and RH remain open.

## Verification

Ubuntu-24.04 WSL2 built the source and audit in the ext4 verification copy:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| renewal-deviation source             |  3401 | PASS   |
| renewal-deviation audit              |     - | PASS   |
| CCM25Concrete aggregate              |  3903 | PASS   |
| full repository                      |  3984 | PASS   |
+--------------------------------------+-------+--------+
```

All seven audited declarations use exactly

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or user axiom was added.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorSingleChannelRenewalDeviation.lean

ConnesWeilRH/Dev/
  ...AntiresonantInteriorSingleChannelRenewalDeviationAudit.lean
```
