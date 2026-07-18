# Proof 373: harmonic midpoint root row

Date: 2026-07-18

Status: exact consumer reduction from a uniform endpoint root-commutator
bound to the near Gate 3U detector row.  It combines Proof 354's canonical
midpoint ideal transfer, Proof 371's positive-detector reduction, and Proof
359's elementary harmonic prime envelope.

The resulting endpoint root theorem is a sufficient Gate producer, not yet a
proved route estimate.  Gate 3U, the finite-`S` sign, Burnol's identity, and
RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| detector square                               | removed via root         |
| midpoint root commutator                      | endpoint transfer        |
| reciprocal prime weights                      | harmonic envelope        |
| Gram inverse                                  | absent                   |
| explicit moving prolate commutator             | absent via Proof 372    |
| endpoint root uniformity                      | open, active producer   |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

Successor audit: Proofs 375--377 prove the endpoint theorem `(MR.6)` by
identifying every actual Euler-prefix Sonin range as nearly invariant and
using its uniform finite-rank Cayley commutator.  Proof 378 then closes this
proof's reciprocal-weight detector row.  It does not join that row to Proof
351's Julia range row: the raw midpoint range corner still needs a same-object
factorization through one common boundary-localized Hilbert--Schmidt root.

## 2. Midpoint ideal transfer

Let `P_(j-1),P_j` be consecutive quotient projections and let `M_j` be Proof
354's canonical midpoint.  For every near prime `p_j>=3`, Proof 354 gives

```text
norm([C,M_j])_2
 <=c_mid(
   norm([C,P_(j-1)])_2+norm([C,P_j])_2),           (MR.1)

c_mid=(sqrt(2)+2)/2.                               (MR.2)
```

The single `p=2` step has its own fixed strict-angle constant and contributes
one fixed term.  It is never inserted into an asymptotic prime sum.

Squaring `(MR.1)` gives

```text
norm([C,M_j])_2^2
 <=2 c_mid^2(
   norm([C,P_(j-1)])_2^2+norm([C,P_j])_2^2).       (MR.3)
```

## 3. Positive detector

For `W=C* C`, Proof 371 applied at `M_j` gives

```text
norm((I-M_j)W M_j)_2^2
 <=2 norm(C)^2 norm([C,M_j])_2^2.                  (MR.4)
```

Combining `(MR.3)--(MR.4)`,

```text
norm((I-M_j)W M_j)_2^2
 <=4 c_mid^2 norm(C)^2(
   norm([C,P_(j-1)])_2^2+norm([C,P_j])_2^2).       (MR.5)
```

No branch of the physical Sonin ledger has been normed separately.

## 4. Uniform endpoint hypothesis

The new source target is

```text
sup_(log(p_j)<=L)
 norm([C_g,P_j])_2^2

 <=C_root(1+L+B_root)^d norm(g)_(H^r)^2.           (MR.6)
```

Under `(MR.6)`, every `p_j>=3` detector term is bounded by

```text
8 c_mid^2 norm(C_g)^2
 C_root(1+L+B_root)^d norm(g)_(H^r)^2.             (MR.7)
```

## 5. Harmonic closure

Proof 359 gives

```text
sum_(log(p)<=L) 1/(p-1)<=1+L.                      (MR.8)
```

Therefore `(MR.7)--(MR.8)` imply

```text
sum_(log(p_j)<=L)
 norm((I-M_j)W M_j)_2^2/(p_j-1)

 <=8 c_mid^2 C_root(1+L)
   (1+L+B_root)^d
   norm(C_g)^2 norm(g)_(H^r)^2,                   (MR.9)
```

plus the fixed `p=2` contribution.  This closes the detector side only.  Proof
351's range Bessel row applies after the range sine receives one common
Hilbert--Schmidt source input.  The raw midpoint range corner is merely
bounded, so one cannot invoke the final Cauchy--Schwarz inequality until the
same-object root-split trace identity is proved.  Proof 336 remains the
far-lane owner.

## 6. Physical meaning of the remaining theorem

The endpoint projection is

```text
P_j=E-R_j.                                         (MR.10)
```

Hence

```text
[C_g,P_j]=[C_g,E]-[C_g,R_j].                       (MR.11)
```

Proof 372 rewrites each orientation of the Sonin root crossing through the
signed outer-minus-second boundary numerator and the genuine boundary polar
Gram.  Thus `(MR.6)` is now a uniform root-level two-boundary theorem.  It is
strictly earlier than the positive detector square and contains no naked
Euler Gram inverse.

## 7. Reproducible certificate

The companion probe uses a sequence of exact two-plane quotient rotations.
It checks

```text
canonical midpoint construction;
midpoint transfer `(MR.1)`;
positive-detector reduction `(MR.4)`;
the weighted harmonic consequence `(MR.9)`.        (MR.12)
```

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/373_harmonic_midpoint_root_row_probe.py
```

The finite sequence verifies the consumer constants.  It is not evidence for
the continuous endpoint theorem `(MR.6)`.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| moving detector variance                      | Proof 370                |
| detector -> root commutator                   | Proof 371                |
| prolate -> boundary polar renewal             | Proof 372                |
| harmonic midpoint consumer                    | closed `(MR.9)`          |
| endpoint root theorem `(MR.6)`                 | Proofs 375--377         |
| reciprocal-weight detector row                | closed                  |
| same-object common-root range factor          | open, active producer   |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
