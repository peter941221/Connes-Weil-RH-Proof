# Proof 384: root-dilation Lean owner

Date: 2026-07-18

Status: generic noncommutative Lean ownership for the two-copy root algebra in
Proof 380.  The module proves the dilation square, the first-copy positive
ordering, and the two root orientations in the anticommutator.

The module deliberately does not encode a trace cycle, a Hilbert--Schmidt
premise, Proof 382's Douglas inequality, or the open CCM24 alignment theorem.
Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| formal two-copy root dilation                 | Lean owner               |
| `C_dagger C` / `C C_dagger` square            | Lean owner               |
| first-copy response ordering                  | Lean owner               |
| anticommutator root orientations              | Lean owner               |
| trace-class cycle `(RD.8)`                    | mathematical contract   |
| Julia insertion/alignment                     | open `(JR.9)/(JR.19)`  |
| aggregate import                              | added                   |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Source module

The new module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSRootDilation.lean                    (RL.1)
```

It works over an arbitrary noncommutative ring.

## 3. Owned definitions

For a root `C`, formal adjoint `C_dagger`, and first-copy difference `A`, Lean
defines

```text
G=[[0,C_dagger],
   [C,0]],

A_1=[[A,0],
     [0,0]].                                       (RL.2)
```

The theorem `rootDilation_mul_self` proves

```text
G G=[[C_dagger C,0],
     [0,C C_dagger]].                              (RL.3)
```

The theorem `rootSquare_mul_firstCopy` proves

```text
G^2 A_1=[[C_dagger C A,0],
         [0,0]].                                   (RL.4)
```

Finally, `rootDilation_firstCopy_anticommutator` proves

```text
G A_1+A_1 G
 =[[0,A C_dagger],
   [C A,0]].                                       (RL.5)
```

No commutation relation is used in `(RL.3)--(RL.5)`.

## 4. Deliberate theorem boundary

Proof 380 additionally uses midpoint blocks and an ordinary trace-class cycle
to obtain

```text
Tr(C* C A)=2 Re <B_root,Y_root>_(S_2).             (RL.6)
```

Encoding `(RL.6)` requires actual Hilbert-space operators, adjoints, Schatten
classes, and a trace.  Storing those analytic facts as fields beside the ring
identities would not formalize them.

Likewise, the module contains no statement resembling

```text
mathcalY_root*mathcalY_root
 <=C^2 mathcalS_A*mathcalS_A.                      (RL.7)
```

Equation `(RL.7)` is Proof 382's open source theorem, not an algebraic axiom.

## 5. Verification results

The unified WSL2 ext4 verification ran:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build \
    ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootDilation \
    ConnesWeilRH.Dev.CCM24FiniteSRootDilationAudit

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CCM25Concrete
```

The focused owner and audit pass with `1200` jobs.  All three audited theorems
report exactly

```text
[propext, Classical.choice, Quot.sound].           (RL.8)
```

The `CCM25Concrete` aggregate passes with `3663` jobs.  The first focused
attempt imported only `Matrix.Basic`, which did not expose the finite-sum
expansion used by 2-by-2 multiplication.  Switching to Mathlib's existing
`Matrix.Notation` pattern and `Fin.sum_univ_succ` closed the implementation
without changing `(RL.3)--(RL.5)`.

## 6. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| reusable root-copy ring algebra               | Lean-owned               |
| Proof 380 trace pairing                       | source mathematics       |
| Proof 381 generic obstruction                 | source mathematics       |
| Proof 383 common root bundle                  | source mathematics       |
| Proof 382 CCM24 alignment                      | open `(JR.9)/(JR.19)`  |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
