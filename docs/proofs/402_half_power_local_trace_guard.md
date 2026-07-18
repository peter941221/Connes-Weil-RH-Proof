# Proof 402: half-power local-trace guard

Date: 2026-07-18

Status: exact two-dimensional counterexample to a generic `p^(-1)` estimate
for the one-step increments from Proof 401.  Even with a positive detector
commuting with the unitary transport and with all one-step Gram bounds, the
projection response has a nonzero `p^(-1/2)` first variation.

This rejects summing local increments by absolute values.  It does not reject
the source-specific outer-minus-Sonin-prolate cancellation, prove Gate 3U,
the finite-`S` sign, Burnol's identity, or RH.

## 1. Exact guard

On `C^2`, take

```text
U=[0 1; 1 0],
P=diag(1,0),
W=I+cU,                 0<c<1.                    (HG.1)
```

Then `U` is unitary and self-adjoint, `W>0`, and

```text
[W,U]=0.                                         (HG.2)
```

For `0<a<1`, let

```text
T_a=I-aU,
P_a=projection onto T_a^(-1)Ran(P).              (HG.3)
```

Since

```text
T_a^(-1)e_1=(1-a^2)^(-1)(e_1+a e_2),            (HG.4)
```

one obtains

```text
P_a=1/(1+a^2) [1 a; a a^2].                     (HG.5)
```

The exact positive-detector response is

```text
Tr[W(P_a-P)]=2ca/(1+a^2).                        (HG.6)
```

Thus

```text
lim_(a->0) a^(-1)Tr[W(P_a-P)]=2c !=0,           (HG.7)

a^(-2)abs Tr[W(P_a-P)] -> infinity.             (HG.8)
```

Putting `a=p^(-1/2)`, the generic local scale is `p^(-1/2)`, not `p^(-1)`.

## 2. Why the guard satisfies the earlier contracts

The probability-normalized inverse

```text
M_a=(1-a)(I-aU)^(-1)                             (HG.9)
```

is a contraction, and its source covariance lies between `rho_a^2I` and
`I`, exactly as in Proof 401.  The detector commutes with both `T_a` and
`M_a`.  Therefore the failure of a quadratic estimate is not caused by
noncommuting transport, loss of positivity, or a conditioned one-step Gram.

What the guard omits is the actual CC20 geometry:

```text
outer boundary
  - Sonin/second-support boundary
  + prolate correction
  + quotient-compression corrections.           (HG.10)
```

Those branches are precisely what Proof 387 keeps in its eleven-atom bracket.

## 3. Gate consequence

For primes below the compact-support cutoff, an absolute half-power sum has
exponential support cost:

```text
sum_(p<=exp(2B)) p^(-1/2)
 approximately exp(B)/B.                         (HG.11)
```

That cannot meet the required polynomial bound in `B`.  By contrast, the
quadratic prime scale has only logarithmic growth:

```text
sum_(p<=exp(2B)) p^(-1)=O(log B).                (HG.12)
```

Consequently a successful proof must cancel or globally recombine the exact
first variation before taking an absolute value.  Proof 401's local inverse
bound alone is insufficient.

## 4. Reproducible certificate

The companion script evaluates `(HG.5)--(HG.8)` over a growing prime list,
checks positivity and commutation, and confirms that the response divided by
`a` tends to `2c` while the response divided by `a^2` grows.

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/402_half_power_local_trace_guard_probe.py
```

## 5. Route judgment

```text
+-----------------------------------------------+---------------------------+
| layer                                         | judgment                  |
+-----------------------------------------------+---------------------------+
| generic local `p^(-1)` response               | false                    |
| positive commuting detector as repair         | false                    |
| uniform one-step Gram bound as repair          | false                    |
| complete first-variation cancellation         | required, source-specific|
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+-----------------------------------------------+---------------------------+
```
