# Proof 379: nearly-invariant commutator Lean owner

Date: 2026-07-18

Status: generic ring-level Lean ownership for the reusable commutator algebra
used in Proofs 376--378.  The module owns the model-projection boundary
difference, the outer-minus-Sonin band difference, and the complement sign.

The Hardy/model-space representation, rank bounds, and Schatten estimates
remain mathematical source arguments rather than Lean theorems.  They close
the endpoint theorem `(MR.6)`, not Gate 3U: the root-split same-object
Hilbert--Schmidt pairing remains open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| model projection commutator                   | Lean owner               |
| outer-minus-Sonin commutator                  | Lean owner               |
| complement commutator sign                    | Lean owner               |
| aggregate import                              | added                    |
| nearly-invariant rank theorem                 | external mathematics     |
| compact-root Sobolev estimate                 | external mathematics     |
| Gate 3U analytic Lean owner                    | open                     |
+------------------------------------------------+---------------------------+
```

## 2. Source module

The new module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSNearlyInvariantCommutator.lean          (NL.1)
```

It works over an arbitrary noncommutative ring and stores no analytic premise.

## 3. Owned identities

For

```text
[C,P]=CP-PC,
P_K=P-Theta P ThetaDagger,                           (NL.2)
```

and commuting relations

```text
C Theta=Theta C,
C ThetaDagger=ThetaDagger C,                         (NL.3)
```

Lean proves

```text
[C,P_K]
 =[C,P]-Theta[C,P]ThetaDagger.                       (NL.4)
```

It also proves

```text
[C,E-R]=[C,E]-[C,R],                                 (NL.5)

[C,I-P]=-[C,P].                                      (NL.6)
```

Equation `(NL.4)` is the algebra behind the model-space rank-two defect.
Equations `(NL.5)--(NL.6)` preserve the signed route orientation.

## 4. Deliberate theorem boundary

The module does not encode any premise such as

```text
rank([z,P_M])<=2,
norm([C_g,P_M])_2<=polynomial.                       (NL.7)
```

Those facts require Hitt--Sarason nearly-invariant space theory, the genuine
Fourier/Mellin carrier, and compact-root Sobolev estimates.  Storing `(NL.7)`
as a structure field would not formalize the analytic proof.

## 5. Verification results

The unified WSL2 ext4 verification ran:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build \
    ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNearlyInvariantCommutator \
    ConnesWeilRH.Dev.CCM24FiniteSNearlyInvariantCommutatorAudit

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CCM25Concrete
```

The focused owner and audit pass with `575` jobs.  All three audited theorems
report exactly

```text
[propext]
```

The `CCM25Concrete` aggregate passes with `3662` jobs.  These builds own only
the algebra in `(NL.4)--(NL.6)`; they do not formalize the analytic rank or
root-split estimates.

## 6. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| reusable noncommutative algebra               | Lean-owned               |
| Proof 375 carrier identification              | source mathematics       |
| Proofs 376--377 analytic estimate             | source mathematics       |
| Proof 378 endpoint `(MR.6)`                   | closed mathematically    |
| reciprocal-weight detector row               | closed mathematically    |
| common-root same-object pairing               | open                     |
| Gate 3U / its Lean formalization              | open / open              |
| finite-S sign / Burnol / RH                    | open / open / open       |
+------------------------------------------------+---------------------------+
```
