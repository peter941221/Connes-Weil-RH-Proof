# Proof 430: weighted translation square ledger

Date: 2026-07-20

Status: the synchronized prime-power square ledger is exact and axiom-clean.
Its direct use as a bound for the linearly expanded Euler generator is
rejected: the available Bessel estimate controls the corresponding weighted
analysis family, while the physical generator is a coherent synthesis.  The
weight transfer needed to identify those two objects pays the prime-cluster
multiplicity exposed by Proof 348.

This proof does not close Gate 3U, prove the finite-S sign, prove Burnol's
identity, or prove RH.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| one genuine generator mode                    | exact coefficient         |
| synchronized-time mode square                 | exact                     |
| complete repetitions at one prime             | summable                  |
| finite visible-prime square ledger             | axiom-clean               |
| weighted localized Bessel theorem              | valid                     |
| raw coherent generator synthesis               | not controlled           |
| direct square-ledger Gate 3U argument           | rejected                  |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Exact mode energy

For a visible prime `p` and `n=m-1`, the actual parameterized generator mode
has coefficient

```text
c_(p,n)(alpha)=-alpha^n p^(-(n+1)/2).             (WT.1)
```

The compact half-line boundary length is `(n+1) log(p)`.  Squaring the
coefficient and integrating synchronized time gives

```text
integral_0^1
  alpha^(2n) p^(-(n+1)) (n+1) log(p) d alpha

 =[(n+1)/(2n+1)] log(p) p^(-(n+1))
 <=log(p) p^(-(n+1)).                              (WT.2)
```

Therefore

```text
sum_(n>=0) integral_0^1 energy_(p,n)(alpha) d alpha
 <=log(p)/(p-1).                                   (WT.3)
```

The Lean source proves `(WT.1)--(WT.3)` for the literal
`parameterizedPrimeEulerGeneratorMode`; it is not a surrogate coefficient
sequence:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSWeightedTranslationBessel.lean
```

## 3. What the Bessel theorem actually says

For localized vectors `v_i`, projections `P_i`, and nonnegative weights
`w_i`, the new theorem proves

```text
sum_i w_i abs(<h,v_i>)^2
 <=E_vector M_local norm(h)^2.                     (WT.4)
```

By Hilbert-space duality, `(WT.4)` is also a synthesis estimate for the same
weighted family `sqrt(w_i) v_i`:

```text
norm(sum_i d_i sqrt(w_i) v_i)^2
 <=E_vector M_local sum_i abs(d_i)^2.              (WT.5)
```

The physical generator instead contains

```text
sum_i c_i v_i.                                     (WT.6)
```

To read `(WT.6)` through `(WT.5)`, one must set

```text
d_i=c_i/sqrt(w_i).                                 (WT.7)
```

Choosing `w_i` to be the square-energy weight makes the analysis ledger
small, but `(WT.7)` moves the missing multiplicity into `sum abs(d_i)^2`.
The weight has not disappeared; it has moved to the synthesis coefficients.

The Lean identities

```text
identicalModes_analysisSquareLedger
identicalModes_coherentSynthesisNormSq
identicalModes_coherentSynthesisGap
```

record the exact finite guard

```text
diagonal square ledger =N,
coherent synthesis square=N^2.                    (WT.8)
```

This generic guard explains the type error.  The source-compatible guard is
stronger.

## 4. Genuine prime-cluster obstruction

Proof 348 uses the actual prime translation modes.  For primes in a short
multiplicative interval

```text
p in [X,(1+epsilon)X],                             (WT.9)
```

their logarithmic displacements differ by at most `log(1+epsilon)`.  A fixed
compact root therefore makes the corresponding boundary vectors nearly
parallel.  The exact asymptotic comparison is

```text
coherent local S2 square >=c X/log(X),
diagonal Euler square ledger =O(1).                (WT.10)
```

The evidence and source-compatible construction are in

```text
docs/proofs/348_prime_cluster_local_s2_obstruction.md
```

Thus no constant independent of the visible prime set can turn the new
diagonal ledger into the norm square of the expanded synchronized generator.

## 5. Fixed-quotient two-branch verdict

Proof 405's exact source corner splits the physical output through the
second-support projection `Q`:

```text
B[W,R]R A B
 =B Q W R A B+B(I-Q)[W,Q]R A B.                   (WT.11)
```

Before the left `B`, the `Q` and `I-Q` coordinates are orthogonal.  This is a
valid physical-branch recombination.  It does not create a different
orthogonal coordinate for every `(p,m)` mode: all prime modes remain inside
the same right transport `A`.  Expanding that transport and applying a norm
therefore recreates `(WT.10)`.

The two-branch owner can become useful only after the complete nonlinear
Gram owner has produced one of the following:

```text
an actual Julia/innovation row indexed by prime steps;

or

an exact extra Euler half-power after the entire
outer - Sonin + prolate + quotient bracket is recombined.          (WT.12)
```

## 6. Route decision

```text
synchronized generator expansion
  -> exact square ledger
  -> coherent synthesis obstruction
  -> stop before taking a modewise norm.

active route
  -> keep Proof 429's literal Gram-order target product whole
  -> repair the fixed-quotient carrier (Proof 431)
  -> seek a nonlinear Julia innovation or prove Proof 416 (EN.7).   (WT.13)
```

The square ledger remains reusable evidence.  It is not a Gate 3U producer.

## 7. Verification

The focused WSL2 target is

```text
ConnesWeilRH.Dev.CCM24FiniteSWeightedTranslationBesselAudit.
```

It audits the exact mode ledger, the localized Bessel theorem, and the three
coherent-synthesis guard identities.  The declarations use only the standard
project axiom set

```text
[propext, Classical.choice, Quot.sound].           (WT.14)
```
