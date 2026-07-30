# Proof 619: antiresonant interior gap normal form

## Result

Proof 619 identifies the sole operator-valued survivor from Proofs 617--618
with the already synchronized metric/forward boundary-moment gap.

Define the genuine interior owner

```text
Interior_(p,S)
  = signedRow_(p,S)
      * (E N_p^dagger E)
      * newFrame_S.
```

Lean proves the exact normal form

```text
Interior_(p,S)
  = Gap_(p,S) * ReverseTransition_(p,S)^dagger,
```

where the gap is kept as the single signed object

```text
Gap_(p,S)
  = boundaryMoment_S * Transition_(p,S)^dagger
    - Transition_(p,S)^dagger * boundaryMoment_(p::S).
```

No summand is bounded separately.

## Two-sided recovery

The reverse and forward transitions satisfy

```text
ReverseTransition^dagger * Transition^dagger = rho_p * I.
```

Therefore

```text
Interior_(p,S) * Transition_(p,S)^dagger
  = rho_p * Gap_(p,S).
```

Since both transitions are contractions and `rho_p >= 1/8`, Lean proves

```text
(1/8) * ||Gap_(p,S)||
  <= ||Interior_(p,S)||
  <= ||Gap_(p,S)||.
```

Equivalently,

```text
||Gap_(p,S)|| <= 8 * ||Interior_(p,S)||.
```

## Route consequence

```text
+----------------------------------+--------------------------------------+
| object                           | status                               |
+----------------------------------+--------------------------------------+
| scalar rho_p^(-1)                | uniformly bounded by 8               |
| exterior renewal F N_p^dagger E  | exactly annihilated                  |
| interior renewal E N_p^dagger E  | absorbed into the synchronized gap   |
| reverse transition               | contractive, scalar-invertible       |
| synchronized metric/forward gap  | unique analytic Bone 1 bottom        |
+----------------------------------+--------------------------------------+
```

Thus the renewal resolvent is no longer an independent analytic obstacle.
A family-uniform bound for `Interior_(p,S)` is equivalent, up to the fixed
factor `8`, to a family-uniform bound for the complete synchronized gap.

## Lean build boundary

The implementation is deliberately split across two source modules:

```text
AntiresonantInteriorGapNormalForm
  -> compiles the exact normal form to an opaque .olean boundary

AntiresonantInteriorGapNormEquivalence
  -> consumes that boundary for reconstruction and norm comparison
```

Keeping the original expanded composition proof in one module triggered a
Lean kernel deterministic timeout.  The downstream reconstruction now uses
the generic operator lemma
`comp_eq_smul_of_eq_comp_and_comp_eq_smul_id`; this reduced its focused
compile time to about `2.5s` without changing any theorem statement.

## Verification

```text
focused source modules and audits: 3387 jobs, PASS
CCM25Concrete aggregate:             3888 jobs, PASS
full repository:                     3969 jobs, PASS
audited axioms: [propext, Classical.choice, Quot.sound]
```

## Boundary

Proof 619 does not prove that this gap is uniformly bounded.  In particular,
it does not estimate the two boundary moments separately, close Bone 1 or
Gate 3U, prove the finite-S sign, prove Burnol's identity, or prove RH.
