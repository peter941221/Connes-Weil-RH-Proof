# Proof 367: compressed-detector boundary ideal

Date: 2026-07-18

Status: exact ideal control of Proof 366's quotient commutator.  If the
ambient normalized Euler inverse is a contraction, the compressed detector
commutator is carried by two copies of the fixed physical boundary
commutator, with uniform Schatten-2 and Schatten-1 bounds.

This proves that the correction is trace legal and has no raw Euler condition
number before Gram normalization.  It does not bound the correction after
composition with the compressed Gram inverse.  Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| quotient commutator owner                     | two boundary copies      |
| normalized ambient Euler norm                 | <=1                      |
| Schatten-2 correction cost                    | <=2 boundary cost        |
| Schatten-1 correction cost                    | <=2 boundary cost        |
| compact-root physical support                 | fixed boundary window    |
| post-Gram uniformity                          | open                     |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Exact owner

Let `E` be the quotient support projection.  Let `V` be the normalized
ambient inverse Euler operator and let `W` be the compact-root detector.
Assume

```text
[W,V]=0,
norm(V)<=1.                                         (BI.1)
```

On `E H`, define

```text
A=E V E,
W_E=E W E.                                         (BI.2)
```

Proof 365 gives

```text
C_E:=[W_E,A]
   =E[W,E]VE+EV[W,E]E.                             (BI.3)
```

The two summands in `(BI.3)` retain their signs and ordering.  No inverse
operator appears.

## 3. Uniform Schatten bounds

Let `J` be either the Hilbert--Schmidt ideal `S2` or the trace-class ideal
`S1`.  The two-sided ideal property gives

```text
norm(E[W,E]VE)_J
 <=norm([W,E])_J norm(V),

norm(EV[W,E]E)_J
 <=norm(V) norm([W,E])_J.                           (BI.4)
```

Therefore

```text
norm(C_E)_J
 <=2 norm(V) norm([W,E])_J
 <=2 norm([W,E])_J.                                 (BI.5)
```

The constant in `(BI.5)` is independent of the visible finite prime set and
of its condition number.  This is a bound on the complete compressed
commutator, not on an expansion into prime words.

## 4. Compact-root boundary cost

For a positive compact-root detector `W=C_g* C_g`, its correlation kernel
`F` satisfies

```text
supp(F) subset [-2B_root,2B_root].                  (BI.6)
```

The boundary commutator has kernel

```text
K_E(x,y)=(1_E(y)-1_E(x))F(x-y).                    (BI.7)
```

If `E` is a half-line, nonzero values in `(BI.7)` force both variables into
the fixed `2B_root` neighborhood of its boundary.  Proofs 261 and 361 supply
the corresponding trace/Hilbert--Schmidt legality.  Equations
`(BI.3)--(BI.5)` transport that legality to the quotient correction without
introducing an infinite half-line root leg.

The Euler factors in `(BI.3)` can move a localized vector after the boundary
crossing.  Thus `(BI.5)` is an ideal budget, not a claim that the final kernel
still has compact support in both variables.

## 5. Remaining Gram issue

Proof 366 needs

```text
(E-P_A)C_E U_0 H_A^(-1/2).                         (BI.8)
```

Equation `(BI.5)` controls `C_E`, but it does not license

```text
norm(C_E U_0 H_A^(-1/2))_2
 <=norm(C_E)_2 norm(H_A^(-1/2)).                   (BI.9)
```

as a uniform route estimate.  The last factor in `(BI.9)` is the rejected
Euler condition number.  The correction must instead be recombined with the
transported fixed crossing before the normalized covariance is estimated.

## 6. Reproducible certificate

The companion probe checks, for compressed commuting normal contractions,

```text
the exact identity `(BI.3)`;
the Frobenius/Schatten-2 bound `(BI.5)`;
the nuclear/Schatten-1 bound `(BI.5)`;
nonzero quotient commutator despite ambient commutation. (BI.10)
```

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/367_compressed_detector_boundary_ideal_probe.py
```

## 7. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| correction trace legality                     | closed                   |
| correction pre-Gram S2/S1 cost                | uniform `(BI.5)`         |
| branchwise prime expansion                    | unnecessary/forbidden    |
| correction plus fixed crossing                | next recombination      |
| post-Gram Douglas domination                  | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
