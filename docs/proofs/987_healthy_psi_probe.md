# 987 - raw bump under the complete Weil functional (SUPERSEDED result corrected)

Date: 2026-08-12. Status: reproducible floating-point diagnostic. RH NOT claimed.
Companion: `docs/proofs/987_healthy_psi_probe.py`.

The earlier `psi ~= 0.86` result is superseded. It used an incorrect pole
coordinate and only the prime-2 term. The current evaluator mirrors
`C1SameOwnerWeil` for a real compact-log test and enforces the defining
identities before printing a value.

## Object and formula

The test is the centered smooth bump supported on `[-1,1]`. For its
autocorrelation square `F = g^* * g`, the evaluator uses:

```text
A              = F(0) = ||g||_2^2
pole(F)        = L_F(+1/2) + L_F(-1/2)
prime_n(F)     = Lambda(n)/sqrt(n) * (F(log n) + F(-log n))
Psi(F)         = pole(F) - arch(F) - sum_(visible prime powers n) prime_n(F)
```

It does not use `i/2`, `F(2)`, or `F(1/2)` as replacements for these
coordinates.

## Result

```text
+------------------------+----------------+
| quantity               | value          |
+------------------------+----------------+
| A = ||g||_2^2          | +1.40570525    |
| arch                   | +3.31370858    |
| pole                   | +4.72287080    |
| all visible primes     | +1.40152344    |
| Psi                    | +0.00763878    |
| max pole identity err  | 1.091e-12      |
| abs(A - ||g||_2^2)     | 1.548e-13      |
+------------------------+----------------+
```

Visible indices are `2, 3, 4, 5, 7`; the last term is numerically zero at the
support boundary. The raw test has moments

```text
M(0)=1.50000000, M(1/2)=1.53669626, M(1)=1.65017411.
```

It is therefore outside the finite-vanishing domain. Its positive value is
neither a proof nor a counterexample to the criterion.

## Verdict

This probe now checks coordinate and component assembly. It contributes no
universal sign theorem. The old `psi ~= 0.86`, `2 Re M(F,i/2)`, and single
`term2` readout must not be used as current evidence. RH NOT claimed.
