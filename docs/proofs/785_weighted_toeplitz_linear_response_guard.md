# Proof 785: Weighted Toeplitz linear-response guard

Date: 2026-08-03

Status: an exact finite Hardy-space guard on the proposed generic
root-relative Toeplitz/Szego route.  Correctly retaining the Toeplitz-kernel
range, its Gram correction, and a positive finite-tap root does not by itself
turn the finite-Euler response from first order into quadratic Euler energy.
The actual CCM24 Hardy--prolate completion may still supply the missing
cancellation; this finite disk model does not contain that real-line geometry.

## 1. Result

```text
+-------------------------------------------------------------+----------------+
| proposed ingredient                                         | status         |
+-------------------------------------------------------------+----------------+
| forward Toeplitz-kernel range q K_Theta                    | retained       |
| Gram-corrected orthogonal projection                       | retained       |
| positive two-tap root W = C_b^* C_b                        | retained       |
| generic quadratic response in the Euler amplitude          | false          |
| actual Hardy--prolate / physical-kernel cancellation        | still open     |
| support-polynomial Gate 3U                                  | open           |
+-------------------------------------------------------------+----------------+
```

The exact model is deliberately minimal:

```text
K_Theta = K_z = span{1},
q_a(z) = 1 - a z,             0 < a < 1,
C_b(z) = 1 + b z,             0 < b < 1,
W_b = C_b^* C_b = |1 + b z|^2.
```

Here `q_a` and `q_a^-1` are bounded analytic multipliers, so the actual
forward Toeplitz-kernel orientation from Proof 769 gives

```text
q_a K_z = span{1-a z}.
```

Let `P_a` be the orthogonal projection onto this line and let `P_0` project
onto `span{1}`.  On the normalized circle measure, direct Gram correction
gives

```text
Tr(W_b(P_a-P_0)) = -2 a b / (1+a^2).                 (LR.1)
```

Consequently

```text
d/da Tr(W_b(P_a-P_0)) at a=0 = -2b,                 (LR.2)
```

which is nonzero for every nontrivial positive two-tap root.

## 2. Exact calculation

Use the orthonormal Fourier vectors `1,z`.  The moved vector is

```text
v_a = 1-a z,
norm(v_a)^2 = 1+a^2.
```

The positive detector has Fourier coefficients

```text
W_b = 1+b^2+b z+b z^-1.
```

Therefore its exact line expectation is

```text
<W_b v_a,v_a>
  = (1+b^2)(1+a^2)-2ab.
```

Gram correction divides by `1+a^2`, while the base line has expectation
`1+b^2`.  Subtracting proves `(LR.1)`:

```text
[(1+b^2)(1+a^2)-2ab]/(1+a^2) - (1+b^2)
  = -2ab/(1+a^2).
```

This is the actual projection formula

```text
P_a = |v_a><v_a| / <v_a,v_a>,
```

not an oblique similarity and not an uncorrected multiplier form.

## 3. What this rules out

The logarithmic Euler symbol has quadratic half-Sobolev energy near `a=0`:

```text
sum_(m>=1) m |a^m/m|^2
  = sum_(m>=1) a^(2m)/m
  = -log(1-a^2)
  = a^2 + O(a^4).                                    (LR.3)
```

But `(LR.1)` is `-2ab+O(a^3)`.  Thus no theorem based only on

```text
forward analytic Toeplitz-kernel transport;
Gram-corrected projection;
positive finite-tap root;
quadratic H^(1/2) energy of log(q_a)
```

can bound this detector response by a constant times the quadratic Euler
energy uniformly as `a -> 0`.

This is the finite counterpart of the distinction already visible in Proof
346: a Szego determinant is quadratic in its own logarithmic symbol, whereas
its derivative in an independent detector direction is generally a mixed,
first-order quantity.  A valid Gate 3U proof needs an additional cancellation
which makes the actual completed physical response different from this generic
line response before an absolute value is taken.

## 4. Relation to the actual Gate

```text
generic disk Toeplitz kernel
    |
    | shows a linear angular response survives
    v
cannot use a generic quadratic ledger alone

actual CCM24 common-log carrier
    |
    | must use the one completed Hardy--prolate kernel K_complete
    v
source-specific cancellation still required for Gate 3U.
```

The guard does not refute the actual route.  It omits all source-specific
facts which are mandatory in Proof 784:

```text
the real-line Hardy--Titchmarsh second support;
the prolate correction;
the coupled outer/reflected/prolate physical kernel;
compact-root locality on that complete kernel;
the selected finite-S source trace.
```

It does establish a hard boundary: Proof 769's correct weighted Toeplitz
carrier is necessary but not sufficient.  The successor theorem must identify
the literal completed physical trace with a source-specific relative
Toeplitz/Wiener--Hopf quantity whose linear angular response cancels.

## 5. Reproduction

The companion certificate evaluates both the direct Gram-corrected line
projection and `(LR.1)`, checks the derivative, and exhibits the divergent
ratio to `a^2` as `a` decreases.

```text
python3 -B docs/proofs/785_weighted_toeplitz_linear_response_guard_probe.py
```

## 6. Route judgment

```text
correct weighted Toeplitz-kernel carrier:              retained;
generic quadratic response from that carrier:          rejected;
CCM24-specific completed physical cancellation:        required;
support-polynomial Gate 3U / finite-S sign / RH:       open.
```
