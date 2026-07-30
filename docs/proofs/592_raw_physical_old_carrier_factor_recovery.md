# Proof 592: Bone 1 factor recovery

## Result

The local raw co-defect factor now recovers the raw factor required by Bone 1.
If

```text
LocalRaw(p,S) = LeftCoDefect(p,S) * F(p,S)
||F(p,S)|| <= B,
```

then the exact reverse Schur--Markov identity gives

```text
RawDefect(p,S) = LeftCoDefect(p,S) * F_raw(p,S)
||F_raw(p,S)|| <= 8 * B.
```

The factor is constructed as

```text
F_raw = - F * ((primeSchurMarkovScalar p)^(-1) * Transition(p,S)).
```

The constant `8` is the existing uniform bound for the scalar-normalized
forward transition.  No inverse of the Julia co-defect is used.

```text
 +------------------------------+
 | local raw factor, bound B    |
 | LocalRaw = LeftCoDefect * F  |
 +--------------+---------------+
                |
                v
 +------------------------------+
 | reverse recovery             |
 | Reverse * ScaledTransition   |
 | = identity                   |
 +--------------+---------------+
                |
                v
 +------------------------------+
 | raw factor, bound 8B         |
 | RawDefect = LeftCoDefect * F |
 +--------------+---------------+
                |
                v
 +------------------------------+
 | old-carrier domination       |
 +------------------------------+
```

The polar slot already converts a non-polar gap factor of bound `B` into a
local raw factor of bound `||detector|| + B`.  Therefore the direct Bone 1
handoff is

```text
non-polar gap factor B
  -> raw co-defect factor 8 * (||detector|| + B)
  -> old-carrier domination.
```

The reverse conversion is also formalized.  At existence level, a finite
uniform old-carrier domination is equivalent to a finite uniform non-polar gap
factor, with numerical constants allowed to change in the two directions.

## Boundary

This proof closes the algebraic and quantitative recovery layer only.  It does
not construct the non-polar gap factor or prove its uniform bound.  Thus Gate
3U, the finite-S sign, Burnol's identity, and RH remain open.

The exact local source obligation is now isolated as the only missing input in
this Bone 1 route; the boundary/transition recovery itself is no longer an
unproved step.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFactorRecovery.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFactorRecoveryAudit.lean
```

The audited declarations use only
`[propext, Classical.choice, Quot.sound]`.
