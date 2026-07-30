# Proof 613: antiresonant geometric boundary readout

## Result

Proof 613 inserts the genuine Euler weights into the Proof 612 blocks and
sums them in operator norm:

```text
G_(p,S)
  = sum_(n >= 0) q_p^(n+1) C V^n newFrame_S.
```

The matching readout is

```text
R_p
  = sum_(n >= 0) q_p^(n+1) scaledB_n,

R_p * ambientLoss^dagger * newFrame_S
  = G_(p,S).
```

This is an unconditional identity on every actual suffix frame.

## Uniform bound

The visible-prime arithmetic gives `q_p <= 3/4`. Together with the linear
Proof 612 cost,

```text
sum_(n >= 0) (n + 1) (3/4)^n = 16
```

and Lean obtains

```text
||R_p|| <= 32.
```

The constant is independent of the prime, suffix list, and Sonin scale.

## Interpretation

```text
+-----------------------------+-------------------------------+
| object                      | status                        |
+-----------------------------+-------------------------------+
| each boundary block C V^n  | readable by Proof 612         |
| complete geometric channel | uniformly readable, bound 32  |
| complete signed numerator   | not identified with channel   |
+-----------------------------+-------------------------------+
```

## Boundary of the result

The geometric boundary is one real renewal channel. The metric-coframe Gram
correction and the remaining signed leakage must still be recombined before
an estimate. Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH
remain open.

## Verification

```text
focused source build: 3377 jobs, PASS
import-facing audit:  3378 jobs, PASS
audited declarations: 11
axioms: [propext, Classical.choice, Quot.sound]
```
