# Proof 586: moving-source old-carrier approximate kernel

## Result

Proof 584's pointwise estimate is uniform over a bounded moving source
sequence. For `x_n` in the source Sonin carrier, assume

```text
0 <= sourceBound
||x_n|| <= sourceBound  for every n
q_(p_n) = ccm24PrimeEulerCoefficient(p_n) -> 0.
```

Then the genuine old-carrier analysis obeys

```text
||W_(p_n) newFrame([], x_n)||
  <= (2 sqrt(q_(p_n)) + 2 q_(p_n)) sourceBound
  -> 0.
```

This is the correct approximate-kernel shape for a source witness that moves
with `log(p_n)`, a translation scale in the global logarithmic carrier. The
source vector may vary with the prime; only its norm is required to remain
uniformly bounded.

## Bone 1 handoff

The actual obstruction is now:

```text
 +----------------------------+
 | bounded moving source x_n  |
 +-------------+--------------+
               |
               v
 +----------------------------+
 | W_(p_n) newFrame x_n -> 0  |
 +-------------+--------------+
               |
               +------------------------------+
               |                              |
               v                              v
 +----------------------------+   +-----------------------------+
 | signed moment lower bound  |   | signed moment -> 0          |
 | >= epsilon eventually      |   | under a uniform quotient    |
 +-------------+--------------+   +-----------------------------+
               |                              |
               +---------------+--------------+
                               v
                 no uniform old-carrier quotient
```

Proof 585's theorem
`noExistsUniformOldCarrierDomination_of_movingSourceMoment_lowerBound`
consumes this exact shape. The moment is still

```text
M_(p_n) oldFrame_(p_n)^dagger newFrame([], x_n),
```

with the signed `rawCoframeBoundaryMoment`; no norm-only replacement or
termwise branch estimate is introduced.

## What remains open

The new theorem does not construct `x_n`, and it does not prove the signed
moment lower bound. The source-specific lemma still needed for Bone 1 is a
genuine CCM24 carrier statement of the form

```text
exists x_n, sourceBound, epsilon > 0,
  ||x_n|| <= sourceBound,
  epsilon <=
    ||M_(p_n) oldFrame_(p_n)^dagger newFrame([], x_n)||
```

for the actual arithmetic sequence `p_n = Nat.nth Nat.Prime n`, with
`q_(p_n) -> 0`. A translated
candidate must first be shown to remain in the source Sonin carrier; an
ambient global-log translation alone is not such a witness.

The carrier-only `canonicalVisiblePrimeSequence` remains only a `p > 1`
sanity sequence; Proof 587 now supplies the genuine arithmetic-prime sequence
and its coefficient decay. Gate 3U, the finite-S sign, Burnol's identity, and
RH remain open.

## Lean evidence

The source declarations are in:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard.lean
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceMomentObstruction.lean
```

The focused audits report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, user axiom, Gate 3U estimate, finite-S sign, Burnol
identity, or RH proof is supplied by this document.

Proof 587 supplies the operator-norm selector that constructs such a bounded
moving source sequence from an eventual strict lower bound for the actual
one-prime moment column.  It does not prove that lower bound.
