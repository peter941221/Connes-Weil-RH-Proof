# 045 — S3 mass face re-priced: OPEN → CLOSED (unconditional, paper) after 1733/1734

Date: 2026-09-20.  This map entry supersedes the S3 producer pricing of
[044](044_two_front_accounting_after_1674.md) row 1 (the `Pi`/analysis front)
and of [043](043_route_map_to_rh_after_1629.md)'s S3 bone.

## 1. What closed

The uniform annular Gram upper bound — 044's row 1, the last open S3
producer — is now supplied unconditionally on paper:

```text
1733  two-sided cosine rule  : hdiag  <=  ONE first moment B(N) of the two
                                 FIXED tails of k_0 and v = Ht k_0
                                 (mass face; n-independent B(N))
1734  the digamma page       : B(N) is FINITE and -> 0 UNCONDITIONALLY.
        - the phase is only evaluated on Re w = 1/4, where the digamma
          series collapses to real sigma = 1/4 sums:
              |psi(w)|  <= gamma_E + (2 pi^2/3)|w - 1|          (linear)
              |psi'(w)| <= 20  (uniform on the line)            (constant)
          - no Stirling/DLMF 5.15.1 needed: linear growth already suffices
            against the Schwartz decay of Fh.
        - theta = m * conj(Fh) is W^{2,1} cap C_0 with theta' -> 0;
        - two IBPs: |v(s)| <= ||theta''||_1 / (4 pi^2 s^2);
        - B(N) <= C_k^2/(4 (a+N)^4) + ||theta''||_1^2/(32 pi^4 (a+N)^2) -> 0
          (correction: 1733 section 5 printed 1/(8 pi^4 X^2); the correct
          constant is 1/(32 pi^4 X^2)).
1734  formal decay leaf      : C1G8R3AnnularTailDecay.lean — the weighted
                                 tail moment, the cubic tail, and the
                                 assembled B(N) -> 0, standard axioms only
                                 (the 1733 skeleton
                                 C1G8R3AnnularTailCosineRule.lean holds the
                                 cosine rule, Bessel, and the annulus split).
```

Chain status after this wave:

```text
hdiag (1733+1734, paper, unconditional)
  -> survivor-core square-sum      (1723 consumer, formal)
  -> endpoint-gate MASS face       (1680 iff chain, formal)
```

## 2. What stays open (re-priced)

```text
+----------------------------------------------------+---------------------+
| object                                             | status              |
+----------------------------------------------------+---------------------+
| S3 mass producer (uniform annular upper bound)     | CLOSED on paper     |
| FULL formal wiring of the closure in Lean          | OPEN: kernel        |
|   (readback, translation-tail identities,          | readback + wing     |
|   1723-consumer instantiation, theta W^{2,1} page) | integrals, then the |
|                                                    | 1723 instantiation; |
|                                                    | Lemmas A/B/C are    |
|                                                    | anchored in-repo    |
|                                                    | (C1XiCenterTwoGamma |
|                                                    | digamma series)     |
| gate sign face (heq sign + index)                  | OPEN on the         |
|                                                    | two-premise exit    |
|                                                    | (1694/1695;         |
|                                                    | C1CenterTwoRHExit); |
|                                                    | untouched here      |
| 0 <= qw; RH                                        | NOT CLAIMED         |
+----------------------------------------------------+---------------------+
```

## 3. Boundary discipline

This is a mass-face closure only.  By the 1694/1695 corrections the endpoint
gate decomposes as mass + sign + index; the sign face is carried by the
committed two-premise exit
(`healthy_spectral_nonneg_sourceRH_of_yoshida_detector`), whose P2 is the
actual RH core.  Nothing in 1733/1734 touches the sign face, the detector
sign field, or `qw`.
