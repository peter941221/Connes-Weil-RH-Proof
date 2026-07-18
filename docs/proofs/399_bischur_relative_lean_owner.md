# Proof 399: bi-Schur relative Lean owner

Date: 2026-07-18

Status: axiom-audited Lean ownership of the noncommutative algebra introduced
in Proofs 395--398.  The module proves two-step paired-product identities,
the local relative-defect factorization, the two-step numerator telescope,
ordered-response readback, coherent-channel cancellation, and paired scalar-
gauge invariance.

The module deliberately contains no positivity, contraction, trace-class,
Schatten, uniform-bound, Gate 3U, finite-`S` sign, Burnol, or RH premise.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| forward/reverse pair composition              | Lean-owned               |
| local relative numerator                      | Lean-owned               |
| two-step noncommutative telescope             | Lean-owned               |
| ordered numerator readback                    | Lean-owned               |
| coherent compression channel                  | cancels in Lean          |
| paired scalar gauge                           | invariant in Lean        |
| uniform relative bound / Gate 3U              | absent / open            |
+------------------------------------------------+---------------------------+
```

## 2. Formal relative numerator

On an arbitrary noncommutative ring, the module defines

```text
relativeNumerator(alpha_old,G,alpha_new,R,rho)

 :=G alpha_new R-alpha_old rho.                  (LO.1)
```

The scalar is written on the right in `(LO.1)` so the local ring identity
needs no hidden centrality assumption.  In the analytic application
`rho=rho_jI`, hence `(LO.1)` is exactly Proof 396 `(BN.11)`.

If

```text
G R=rho,                                         (LO.2)
```

then Lean proves

```text
relativeNumerator(...)
 =(G alpha_new-alpha_old G)R.                    (LO.3)
```

This is the formal owner of `f_j=e_jR_j`.

## 3. Paired products

For two chronological factors, the module proves both orientations

```text
(G_1G_2)(R_2R_1)=rho_1rho_2,
(R_2R_1)(G_1G_2)=rho_1rho_2,                     (LO.4)
```

from the two local pair identities and the explicit commutations needed to
move scalar factors.  Induction gives Proof 395 `(MI.15)` for every finite
cascade.  The scalar commutations are hypotheses of the generic ring lemma;
they are automatic for the real scalars in the source theorem.

## 4. Two-step telescope

For consecutive compressions `alpha_0,alpha_1,alpha_2`, Lean proves

```text
N_12
 =G_1N_2R_1+N_1rho_2,                            (LO.5)
```

where

```text
N_j=G_jalpha_jR_j-alpha_(j-1)rho_j.              (LO.6)
```

The only commutation used in `(LO.5)` is

```text
rho_2R_1=R_1rho_2.                               (LO.7)
```

Iteration owns the full telescope of Proof 396 `(BN.17)`.  No trace cycle or
norm estimate appears in the proof.

## 5. Ordered response and scalar cancellation

If the reverse product is represented as

```text
Lambda=Gamma^(-1)rho,                            (LO.8)
```

Lean proves

```text
mathcalN
 =(Gamma alpha Gamma^(-1)-alpha_0)rho.           (LO.9)
```

For a coherent compression `alpha` commuting with `G`, `(LO.2)` also gives

```text
relativeNumerator(alpha,G,alpha,R,rho)=0.        (LO.10)
```

This is the ring-level content of Proofs 396 and 397's scalar guard.

## 6. Gauge invariance

Let `c,c_inv` be a central paired gauge with `c c_inv=1`.  The module proves

```text
relativeNumerator(alpha_0,cG,alpha_n,R c_inv,rho)

 =relativeNumerator(alpha_0,G,alpha_n,R,rho).     (LO.11)
```

The generic lemma states the exact commutation with the completed numerator
rather than assuming a commutative operator ring.  Real scalar gauges satisfy
that condition automatically.

## 7. Lean owner and audit

The implementation lives in

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSBiSchurRelative.lean
```

The audit imports that module and prints the axioms of all seven public
theorems.  It is run only after Proofs 395--399 are complete, together with
the four numerical probes and the owning aggregate.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| paired and relative ring algebra              | closed in Lean           |
| scalar-gauge cancellation                     | closed in Lean           |
| Proof 398 fixed-S analytic root legality       | mathematical owner       |
| uniform rho gain `(RL.19)`                    | open, no stored premise  |
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+------------------------------------------------+---------------------------+
```
