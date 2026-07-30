# Proof 589: one-prime moment-column decay

## Result

The Bone 1 selector column from Proof 588 has the opposite behavior from the
required eventual lower bound.  For every selected Weil-square owner, Sonin
scale, and visible arithmetic prime `p`, Lean proves

```text
||onePrimeBoundaryMomentColumn owner lambda p||
  <= 196 * q_p * ||detectorOperator owner||,

q_p = ccm24PrimeEulerCoefficient p = p^(-1/2).
```

Along the actual arithmetic sequence

```text
p_n = Nat.nth Nat.Prime n,
```

`q_(p_n) -> 0`.  The squeeze theorem therefore gives

```text
||onePrimeBoundaryMomentColumn owner lambda p_n|| -> 0.
```

Consequently, the source theorem required by the Proof 588 selector is false
for this column:

```text
not (exists epsilon > 0,
  eventually epsilon <
    ||onePrimeBoundaryMomentColumn owner lambda p_n||).
```

This is a negative result for the current Bone 1 witness route: the selected
column cannot provide the required persistent signed response.

```text
 +-----------------------------+
 | one-prime source column C_p |
 +--------------+--------------+
                |
                v
 +-----------------------------+
 | ||C_p|| <= 196 q_p ||D||    |
 +--------------+--------------+
                |
                v
 +-----------------------------+
 | q_(Nat.nth Prime n) -> 0     |
 +--------------+--------------+
                |
                v
 +-----------------------------+
 | ||C_(p_n)|| -> 0             |
 +--------------+--------------+
                |
                v
 +-----------------------------+
 | no eventual positive lower  |
 | bound for this selector     |
 +-----------------------------+
```

## Bound chain

The proof keeps the signed physical boundary moment as one operator.  It does
not estimate the two signed summands separately and does not replace the
moment by an absolute-value surrogate.

```text
forward coframe                    <= 2 q_p
normalized covariance gap          <= 12 q_p
normalized metric leakage          <= 12 q_p
raw metric leakage                 <= 192 q_p
forward endpoint minus inclusion   <= 194 q_p
raw one-prime moment               <= 196 q_p ||D||
frame adjoints and new frame       <= 1
one-prime column                   <= 196 q_p ||D||
```

The single-prime family is reduced to `visiblePrimes = [p]`.  Its lower Euler
factor is `1 - q_p`; the proof uses `q_p <= 3/4`, hence the inverse factor is
bounded by `4`.  This is why the finite-S covariance estimate remains uniform
enough to produce the explicit `196` constant.

## Lean owners

The source module is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay.lean
```

The import-facing audit is:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecayAudit.lean
```

The aggregate import is in:

```text
ConnesWeilRH/Source/CCM25Concrete.lean
```

The audited declarations use the standard axiom set:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or user axiom is used.

## Boundary of the result

This closes only the proposed Proof 588 column fork.  It does not prove a
uniform old-carrier quotient, Gate 3U, the finite-S sign, Burnol's identity,
or the Riemann Hypothesis.  A different moving source column could still be
studied, but it must not be identified with this decaying column without a
new source theorem.
