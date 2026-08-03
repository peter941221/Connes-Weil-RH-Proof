# Proof 768: Canonical Support Gate 3U

## Result

The result is good but weaker than the intended analytic Gate: Proof 768
closes the literal pointwise `canonicalRealGate3UAt` proposition introduced
by Proof 761.  It does not supply Proof 761's intended support-polynomial
majorant, nor the older complex-trace contract quantified over arbitrary
unrelated finite prime families.

For the exact family selected by one compact Weil square, Lean proves

```text
abs(Re Tr_source(Target_canonical))
  <= 16^(ceil(exp(B)) + 1)
     * (6 + 2 H_lambda)
     * (c-a)^2 * seminorm_(0,0)(g)^2.              (768.1)
```

Here:

```text
B        = owner.supportRadius,
H_lambda = sum_i ||sourceProlateHilbertSchmidtFactor(e_i)||^2,
supp(g)  subset [a,c].
```

The theorem proving `(768.1)` is

```text
canonicalRealGate3UAt_of_supportMajorant.
```

It proves the literal proposition `canonicalRealGate3UAt`; the right side is
defined before the target trace is inspected.

## Why It Works

The existing raw endpoint theorem already gives

```text
abs(Re Tr(Target_canonical))
  <= lowerFactor(canonicalFamily)^(-2) * physicalRootEnergy.   (768.2)
```

The previously nonuniform term becomes support-controlled after restricting
to the exact canonical family.  Every visible Euler coefficient satisfies

```text
0 <= a_p <= 3/4,
```

so each lower factor is at least `1/4` and

```text
lowerFactor(S)^(-2) <= 16^(length S).                         (768.3)
```

Every visible prime comes from a nonzero selected atom `p^m`.  The exact
compact-support theorem therefore gives

```text
log p <= m log p <= B,
length(canonical visible primes)
  <= ceil(exp(B)) + 1.                                        (768.4)
```

Combining `(768.2)`--`(768.4)` proves `(768.1)`.

```text
compact arithmetic support
          |
          v
canonical visible-prime cardinality
          |
          v
explicit lower-factor inverse bound
          |
          v
existing raw endpoint support estimate
          |
          v
canonicalRealGate3UAt
```

## What Is Not Used

The proof does not use:

```text
hsourceAmbientCycle,
Proof 262's dual-coframe carrier identification,
Proof 767's transported-outer projection collapse,
branchwise outer/reflected/prolate estimates,
an existential bound chosen from the target trace.
```

Thus the canonical real Gate bound is independent of the open
source-to-ambient ordinary-trace cycle.

## Scope Guard

The constant in `(768.1)` is deliberately coarse.  It grows like

```text
16^(O(exp(B))).
```

This is adequate for the literal pointwise proposition formalized by Proof
761.  It is not the polynomial-in-`B` bound that Proof 761 identifies as the
intended Yoshida-sequence input: `16^(ceil(exp(B))+1)` grows much faster than
every polynomial in `B`.  No downstream Lean consumer currently turns this
coarse pointwise bound into the finite-S sign.

The theorem also does not prove an `S`-independent estimate for arbitrary
families containing primes unrelated to the selected compact support, the
source/ambient trace cycle, the finite-S semilocal sign, Burnol's identity,
or the Riemann Hypothesis.  A genuine analytic closure still has to exploit
the complete signed boundary cancellation before the first absolute value;
the raw lower-factor estimate used here cannot provide polynomial support
growth.

## Lean Declarations

```text
finiteEulerLowerFactor_inv_sq_le_sixteen_pow_length
canonicalVisiblePrime_log_le_supportRadius
canonicalVisiblePrimes_length_le_supportCardinality
canonicalFiniteEulerLowerFactor_inv_sq_le_supportCardinality
canonicalRealGate3USupportMajorant
canonicalRealGate3UAt_of_supportMajorant
```

## Status

```text
+------------------------------------------------+----------+
| statement                                      | status   |
+------------------------------------------------+----------+
| canonical-family lower-factor support bound    | PROVED   |
| literal `canonicalRealGate3UAt` at (768.1)      | PROVED   |
| intended support-polynomial canonical Gate 3U  | OPEN     |
| arbitrary-family uniform complex Gate          | OPEN     |
| source/ambient ordinary-trace cycle             | OPEN     |
| Proof 262 dual-coframe carrier identity         | OPEN     |
| finite-S semilocal sign                         | OPEN     |
| Riemann Hypothesis                              | UNPROVED |
+------------------------------------------------+----------+
```
