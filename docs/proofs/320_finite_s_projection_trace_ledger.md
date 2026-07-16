# Proof 320: Finite-S Projection/Trace Ledger

## Result

Proof 320 places the actual finite-S CCM24 Sonin projection geometry and the
selected finite prime-power crossing sum on the same common-log Hilbert
carrier.

For a finite family of prime powers, its visible-prime list is derived from
the same terms used by the arithmetic operator.  The resulting operators are

```text
E       = radial support projection
Q_0     = archimedean Fourier-support projection
Q_S     = semilocal Fourier-support projection
R_0     = archimedean Sonin projection
R_S     = semilocal Sonin projection
K_0     = E Q_0 E - R_0
K_S     = E Q_S E - R_S.
```

The finite-S projection is read back through the bounded-invertible CCM24
transport as the Gram-corrected frame projection

```text
R_S = A (A^dagger A)^(-1) A^dagger.
```

Both prolate remainders have the exact positive factorizations

```text
K_0 = (E - R_0) Q_0 (E - R_0),
K_S = (E - R_S) Q_S (E - R_S).
```

Consequently the actual band difference satisfies

```text
R_S - R_0 = E(Q_S - Q_0)E - (K_S - K_0).
```

## Same-Object Trace Readback

Let `W` be the genuine positive convolution detector constructed from the
selected Weil-square owner.  The module defines, rather than assumes,

```text
projectionResponse = W (R_S - R_0)
arithmeticOperator = selected finite prime-power crossing sum
canonicalResidual  = projectionResponse - arithmeticOperator.
```

For a named Hilbert basis and an explicit trace-class witness for the full
projection response, the final theorem proves

```text
Tr(W (R_S - R_0))
  = sum_(p,m) finitePrimeTerm(p^m) + Tr(canonicalResidual).
```

The arithmetic trace legality follows from the existing compact crossing
construction.  Residual trace legality is derived by subtraction; it is not a
field or stored premise.

## Proof Flow

```text
+--------------------------------------------------------------+
| one finite prime-power family                                |
|  terms -> visible primes -> actual CCM24 finite-S transport   |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| common-log projection geometry                              |
|  R_S - R_0 = E(Q_S-Q_0)E - (K_S-K_0)                       |
|  K_0 >= 0, K_S >= 0                                         |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| selected detector and arithmetic crossing operator           |
|  same carrier, canonical operator difference                 |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| ordinary trace ledger                                        |
|  projection trace = finite-prime sum + residual trace        |
+--------------------------------------------------------------+
```

## Remaining Bottom

Proof 320 does not prove that the canonical residual vanishes or is
nonpositive.  It also does not prove Gate 3U, the finite-S sign, Burnol's
identity, or the Riemann Hypothesis.  The next analytic producer must control
the displayed residual on this exact carrier and for this exact detector.

```text
RH = UNPROVED
```
