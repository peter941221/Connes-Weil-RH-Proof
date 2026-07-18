# Proof 362: reflected second-support Douglas factor

Date: 2026-07-18

Status: exact transport of Proof 361's compact-window Douglas factor to the
genuine CC20 second-support projection.  Hardy--Titchmarsh conjugation does
not commute with the detector; instead it turns the selected detector into
the positive convolution square of the explicit reflected compact root.

This closes finite propagation and Douglas domination for the raw second
support.  The compressed second-support/prolate signed remainder remains to be
recombined.  Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain
open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| genuine second-support projection             | H E H                    |
| conjugated selected detector                   | reflected compact square |
| scattering phases                              | cancel exactly           |
| reflected intermediate window                  | finite                   |
| second-support Douglas domination              | exact                    |
| second-support/prolate signed remainder         | still coupled            |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
## 2. Genuine scattering conjugation

Let

```text
H=archimedean Hardy--Titchmarsh involution,
H*=H,
H^2=I,                                              (RS.1)
```

and let `E` be the radial half-line support projection.  The genuine source
second-support projection is

```text
Q_f=H E H.                                          (RS.2)
```

For the selected compact root `g`, put

```text
W_g=C_g* C_g.                                       (RS.3)
```

It is generally false that `[H,W_g]=0`.  The repository proves the correct
identity

```text
H W_g H=W_gref=C_gref* C_gref,                      (RS.4)
```

where `g_ref(x)=g(-x)` with the route's involution/conjugation convention.
The archimedean scattering phases cancel in the spectral multiplier before
`W_gref` is read back as whole-line convolution.

The Lean owners are

```text
sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation,
hardyTitchmarshConjugatedDetector_eq_reflectedPositive
```

in `CCM24RadialBoundaryPairTransport.lean` and
`CCM24ReflectedCompactRoot.lean`.

## 3. Oriented crossing readback

Let

```text
D_second=(I-Q_f)W_g Q_f.                            (RS.5)
```

Using `(RS.1)--(RS.4)`,

```text
D_second
 =H [(I-E)W_gref E] H.                             (RS.6)
```

No trace cycle is used.  Equation `(RS.6)` is an operator conjugation of the
oriented boundary crossing.

## 4. Reflected compact window

Assume

```text
supp(g) subset [-B,B].                              (RS.7)
```

Then `supp(g_ref) subset [-B,B]`.  Apply Proof 361 to the bracket in `(RS.6)`:

```text
(I-E)W_gref E
 =(I-E)C_gref* E_B C_gref E,
E_B=1_[-B,B].                                       (RS.8)
```

Define

```text
A_ref=E_B C_gref E H,
B_ref=H(I-E)C_gref* E_B.                            (RS.9)
```

Then

```text
D_second=B_ref A_ref,                               (RS.10)
norm(B_ref)<=norm(C_gref),                          (RS.11)

D_second*D_second
 <=norm(C_gref)^2 A_ref*A_ref.                     (RS.12)
```

Moreover,

```text
norm(A_ref)_2^2<=2B norm(g_ref)_2^2
                     =2B norm(g)_2^2.               (RS.13)
```

Thus scattering preserves the polynomial compact-support budget, but through
the reflected root and an actual unitary coordinate change.

## 5. Two-copy common envelope

The outer and second-support factors need not be falsely identified.  Bundle
them as

```text
A_boundary x=(A_out x,A_ref x),                     (RS.14)
```

on the orthogonal direct sum of two finite-window carriers.  Then

```text
norm(A_boundary)_2^2
 <=4B norm(g)_2^2.                                  (RS.15)
```

Any fixed signed combination of the two oriented crossings factors through
`A_boundary`; its left factor retains the signs before one final norm.

For a near translated family, Proof 357 enlarges each copy to its common
envelope.  The number of copies is fixed and does not depend on the visible
prime set.

## 6. Coupling guard

The source ledger does not contain the raw second-support commutator in
isolation.  The repository's exact remainder is

```text
E [Q_f,W_g] E-[K_prol,W_g].                         (RS.16)
```

and `CCM24RadialBoundaryPairTransport.lean` deliberately keeps `(RS.16)` as
`sourceSecondSupportProlateRemainder`.  Equations `(RS.10)--(RS.15)` establish
the second-support factor and its budget; they do not authorize discarding
the prolate term or changing the sign in `(RS.16)`.

The next batch constructs a fixed Hilbert--Schmidt factor for the prolate
commutator so the signed pair can be bundled before its final norm.

## 7. Reproducible certificate

The companion zero-fill probe uses spatial reflection as a finite
Hardy--Titchmarsh model.  It checks

```text
Q_f=H E H;
H W_g H=W_gref for the reflected convolution root;
the crossing conjugation `(RS.6)`;
the reflected factorization and Douglas inequality;
the two-copy Hilbert--Schmidt budget.                (RS.17)
```

Run only in the unified verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/362_reflected_second_support_douglas_factor_probe.py
```

The actual Hardy--Titchmarsh/scattering identity is already a Lean theorem;
the probe checks the operator ordering in a finite reflection model.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| reflected compact-root readback               | existing Lean theorem    |
| raw second-support window factor               | closed `(RS.10)`         |
| two-copy boundary envelope                     | polynomial `(RS.15)`     |
| second-support/prolate recombination            | next batch              |
| full quotient domination                       | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
