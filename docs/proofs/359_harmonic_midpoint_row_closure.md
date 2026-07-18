# Proof 359: harmonic midpoint-row closure criterion

Date: 2026-07-18

Status: exact abstract closure of the near Gate 3U estimate from one uniform
common-envelope factorization.  A second detector-side Bessel telescope is
unnecessary: the reciprocal Julia weights have an elementary harmonic bound.
Together with Proof 351's range Bessel row and Proof 357's common finite-window
Hilbert--Schmidt input, a uniform factorization of the complete Proof 358 row
implies the required polynomial near estimate.

The uniform complete-row factorization is not yet proved.  Gate 3U, the
finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| range-side Julia Bessel row                   | Proof 351, constant one   |
| detector reciprocal prime weights              | elementary harmonic bound|
| common near HS input                           | Proof 357                |
| abstract near closure                          | exact                     |
| second detector Bessel telescope               | unnecessary              |
| complete uniform factorization                 | open, sole near producer |
| Lean weighted-row consumer                     | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Harmonic prime envelope

Let `L>=log(2)` and let the visible near primes satisfy `log(p)<=L`.  Since
the primes are a subset of the integers from `2` through `floor(exp(L))`,

```text
sum_(log(p)<=L) 1/(p-1)
 <=sum_(n=1)^(floor(exp(L))-1) 1/n
 <=1+log(floor(exp(L))-1)
 <=1+L.                                             (HC.1)
```

No prime number theorem, Mertens theorem, lower prime spacing, or asymptotic
constant is used.  The deliberately coarse last bound is polynomial in the
support scale, which is all Gate 3U requires.

## 3. Uniform common-factor hypothesis

Let `D_j` be Proof 354's completed midpoint detector row after Proof 355's
half-angle split and Proof 358's physical commutator recombination.  Let

```text
A_(g,L):H_aux->H_source                            (HC.2)
```

be Proof 357's common near-envelope operator.  Its Hilbert--Schmidt square
satisfies

```text
norm(A_(g,L))_2^2
 <=C_0(L+2B_root) norm(g)_(H^r)^2.                 (HC.3)
```

The exact remaining source producer is

```text
D_j=B_j A_(g,L),
sup_j norm(B_j)<=C_1(1+L+B_root)^d,                 (HC.4)
```

where every `B_j` is constructed from the complete signed quotient bracket,
not separately from its outer, Sonin, prolate, residue, or anomaly branches.

## 4. Detector-row closure

Equations `(HC.1)--(HC.4)` imply

```text
sum_(log(p_j)<=L) norm(D_j)_2^2/(p_j-1)

 <=C_1^2(1+L+B_root)^(2d)
   norm(A_(g,L))_2^2
   sum_(log(p_j)<=L)1/(p_j-1)

 <=C_0 C_1^2
   (1+L)(L+2B_root)(1+L+B_root)^(2d)
   norm(g)_(H^r)^2.                                (HC.5)
```

This is the detector-side estimate requested by Proofs 351--354.  It is
uniform in the finite set and polynomial in the near/support scale.

## 5. Final near pairing

Let `R_j` be the pulled-back Julia range row.  Proof 351 gives

```text
sum_j (p_j-1)norm(R_j)_2^2<=norm(A_range)_2^2.       (HC.6)
```

Proof 354 gives the same-object scalar identity

```text
Q_near=sum_j 2 Re <D_j,R_j>_S2.                    (HC.7)
```

One final direct-sum Cauchy--Schwarz inequality, and only one, yields

```text
abs(Q_near)
 <=2 norm(A_range)_2
   [sum_j norm(D_j)_2^2/(p_j-1)]^(1/2).             (HC.8)
```

Substituting `(HC.5)` into `(HC.8)` closes the near Gate 3U bound with a
polynomial constant.  Proof 336 supplies the already closed far lane after
the same-object near/far split.

## 6. Why a second Bessel telescope is unnecessary

Proof 356 shows that individual old detector crossings can be amplified by a
one-step Euler condition number, so a constant-one detector telescope is not
available from commutation alone.  But Gate 3U never asks for such a theorem.

The reciprocal weights already pay for the number of near prime steps:

```text
uniform complete-row factorization
  +harmonic weight sum
  +one common finite-window HS input
  =polynomial detector row.                         (HC.9)
```

Trying to prove more risks reintroducing the false contraction rejected by
Proof 356.

## 7. Exact remaining producer

All five batches reduce the near problem to one statement:

```text
For the literal Proof 343 prefix projections and the literal compact-root
detector, construct B_j such that

  (I-Q_j)WQ_j=B_j A_(g,L),

  sup_j norm(B_j)<=C(1+L+B_root)^d,                 (HC.10)

after the complete Proof 358 bracket is recombined.
```

The equality in `(HC.10)` must retain the canonical midpoint, the prefix Gram
normalization, Proof 335's residue cancellation, and the boundary anomaly.
It cannot be installed as a structure field or route premise.

Once `(HC.10)` is proved, `(HC.1)--(HC.8)` close the near lane and Proof 336
closes the far lane.  That would close Gate 3U.  At present `(HC.10)` is open.

## 8. Lean consumer

The generic weighted-row arithmetic is formalized in

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSHarmonicDetectorRow.lean               (HC.11)
```

It proves that nonnegative row energies bounded pointwise by one common
constant are bounded after weighting by that constant times the total weight.
The module intentionally does not manufacture `(HC.10)` or encode a prime
sum as a premise.

The owning WSL2 build passes with `2343` jobs.  The focused audit reports the
project's allowed axiom set

```text
[propext, Classical.choice, Quot.sound].            (HC.11a)
```

The `CCM25Concrete` aggregate, including Proofs 352, 354, and 359, passes with
`3660` jobs.  No full default build was run.

## 9. Reproducible certificate

The companion script

```text
checks `(HC.1)` for several prime cutoffs;
constructs random contraction rows B_j and one common matrix A;
checks the detector energy bound `(HC.5)`;
checks the final paired Cauchy--Schwarz bound `(HC.8)`. (HC.12)
```

Run in the unified verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/359_harmonic_midpoint_row_closure_probe.py
```

At prime cutoff `10000`, the reciprocal weight is `3.2562068001` versus the
elementary bound `10.210340372`; all row, pairing, and harmonic violations are
zero.  The random common-factor row uses about `0.2894361` of its bound.

The random contraction row is a consumer test, not evidence for `(HC.10)`.

## 10. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| reciprocal-prime harmonic bound               | closed `(HC.1)`          |
| common near HS budget                          | Proof 357               |
| weighted detector-row consumer                 | closed                  |
| final near Cauchy--Schwarz                      | Proof 351 + `(HC.8)`    |
| complete uniform factorization `(HC.10)`       | open, sole near bottom |
| Proof 336 far lane                             | closed                  |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
