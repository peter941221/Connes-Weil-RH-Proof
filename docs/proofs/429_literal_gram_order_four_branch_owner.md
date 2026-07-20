# Proof 429: literal Gram order and four-branch owner

Date: 2026-07-20

Status: formal-integrity repair and actual-carrier completion of Proof 428.
The fixed-`S` route response now has a placeholder-free four-coordinate
Hilbert--Schmidt owner, and its literal right Gram order is connected to the
actual target-commutator owner by adjoint passage and equality of absolute
ordinary traces.

This proof does not establish the uniform signed estimate, close Gate 3U,
prove the finite-`S` sign, prove Burnol's identity, or prove RH.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| outer reflected branch has an independent coordinate | repaired             |
| common boundary pair contains all four physical terms | axiom-clean          |
| fixed-S source response is trace legal                | axiom-clean          |
| left Gram order is the adjoint of route right order    | exact                |
| absolute ordinary traces agree                         | exact                |
| Proof 428 instantiated on literal rectangular carriers | exact                |
| target commutator has fixed-S trace legality           | exact                |
| uniform signed target-product estimate                 | open                 |
| Gate 3U / finite-S sign / Burnol / RH                  | open / open / open   |
+------------------------------------------------------+----------------------+
```

The completed ownership chain is

```text
four physical boundary coordinates
  -> one Hilbert--Schmidt pair product
  -> route right-ordered source response
  -> adjoint left-ordered response
  -> literal target-projection commutator.              (GO.1)
```

## 2. Four physical coordinates

The common pair carrier previously represented

```text
outer + (second-support + prolate).                     (GO.2)
```

The physical commutator ledger has an independent reflected-outer term.  The
correct carrier is therefore the balanced orthogonal sum

```text
(outer + reflected-outer) + (second-support + prolate). (GO.3)
```

The balance in `(GO.3)` is computational, not mathematical: it keeps the
maximum recursive `WithLp` depth equal on both sides.  A right-nested
four-coordinate tree made a later `PiLp` topology search exceed Lean's
instance-synthesis budget.

The reflected-outer pair is not built from the reflected compact root.  It is
the negative adjoint of the ordinary outer pair:

```text
Pair_ref=swap(Pair_outer) with right scalar -1,
TraceProduct(Pair_ref)=-TraceProduct(Pair_outer)*.       (GO.4)
```

The reflected compact root belongs to the second-support branch.  Keeping
that distinction gives

```text
TraceProduct(Pair_all)
 =outer+reflected-outer+second-support+prolate
 =cc20ThreeBranchCommutator.                            (GO.5)
```

Here `three branch` is the historical algebra name: the outer contribution
has two physical orientations, so its Hilbert--Schmidt carrier has four
coordinates.

## 3. The Gram-order mismatch

Let

```text
J     = source Sonin inclusion,
T     = complete finite Euler transport,
K     = T J,
G     = K* K,
W_0   = J* W J.                                       (GO.6)
```

The route stores the inverse Gram on the right:

```text
Q_right=K* W K G^-1-W_0.                              (GO.7)
```

Proofs 427--428 naturally produce the left order

```text
Q_left=G^-1 K* W K-W_0.                               (GO.8)
```

These operators need not be equal.  Since `G^-1`, `K*WK`, and `W_0` are
self-adjoint,

```text
Q_left=Q_right*.                                      (GO.9)
```

For the route-band orientations `B_right=-Q_right` and `B_left=-Q_left`, the
ordinary diagonal trace in the same Hilbert basis satisfies

```text
Tr(B_left)=conj(Tr(B_right)),
abs(Tr(B_left))=abs(Tr(B_right)).                     (GO.10)
```

Equation `(GO.10)`, not an infinite-dimensional trace cycle, transports a
Gate 3U absolute bound between the two Gram orders.

## 4. Literal rectangular instantiation

The abstract Proof 428 theorem places every symbol in one noncommutative
ring.  That is not a legal direct instantiation of the route because

```text
J : sourceSoninCarrier -> finiteSCarrier               (GO.11)
```

is rectangular.  The new rectangular theorem keeps separate source and
ambient Hilbert types.  With `A=T^-1` and

```text
P=T J G^-1 J* T*,                                     (GO.12)
```

it uses only

```text
J*J=I,
A T=I,
P^2=P,
P T J=T J,
T W=W T.                                              (GO.13)
```

Direct composition then proves on the actual carriers

```text
Q_left
 =-J* A (I-P) (W P-P W) T J.                         (GO.14)
```

The instantiated `P` in `(GO.14)` is the canonical finite-`S` orthogonal
Sonin projection, not an oblique similarity and not an abstract placeholder.

## 5. Trace legality

The repaired four-coordinate pair proves that `B_right` is trace legal for
every fixed finite prime-power family.  Adjoint stability gives trace
legality of `B_left`; negation and `(GO.14)` then give trace legality of the
literal target-commutator response.

Consequently

```text
abs Tr(-J* A (I-P) (W P-P W) T J)
 =abs Tr(B_right).                                    (GO.15)
```

This is a same-object statement.  No separately undefined trace of a raw
translation, projection difference, or Gram-normalized summand is introduced.

## 6. Why Proof 376 is not enough

Proof 376 gives a uniform Hilbert--Schmidt estimate for `[W,P]` when `P` is a
nearly invariant target projection.  Equation `(GO.14)` now connects that
result to the route's literal response.  It still does not license

```text
norm(J*A) norm([W,P])_2 norm(TJ)                      (GO.16)
```

as a trace bound.  The transported frame retains the complete Euler history,
and the first and last factors are not a uniformly controlled
Hilbert--Schmidt pair.  Taking norms factor by factor repeats the
condition-number failure exposed by Proof 417.

The open analytic theorem remains a signed scalar estimate for the whole
product in `(GO.14)`, with compact root support used before the first absolute
value.

## 7. Lean ownership

The repaired pair owner is in

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCommonBoundaryPair.lean
```

The Gram-order and rectangular target bridge is in

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGramOrderingBridge.lean
```

The focused audit is

```text
ConnesWeilRH/Dev/CCM24FiniteSGramOrderingBridgeAudit.lean.
```

It checks the reflected pair, the complete pair sum, fixed-`S` trace
legality, the rectangular collapse, both Gram-order adjoint identities, both
absolute-trace identities, and target-response trace legality.

## 8. Route verdict

```text
What is closed:
  all physical commutator coordinates occur in the common pair;
  the formal source tree contains no proof placeholder;
  fixed-S trace legality reaches the literal target commutator;
  left and right Gram orders have exactly the same absolute trace;
  Proof 428 is instantiated on the actual rectangular carriers.

What remains open:
  a uniform signed scalar estimate for the whole target product;
  Proof 416 (EN.7), Gate 3U, and the finite-S sign;
  the same-object arithmetic identity and negative-owner integration;
  Burnol's all-zero identity and unconditional RH.
```

## 9. Verification

The Windows source was copied one way into the isolated Ubuntu 24.04 ext4
verification directory.  The batched Lean acceptance is

```text
+------------------------------------------------+------+
| target                                         | jobs |
+------------------------------------------------+------+
| focused Gram-order/four-branch axiom audit     | 3215 |
| fixed-quotient input-side downstream consumer  | 3218 |
| fixed-source downstream consumer               | 3258 |
| CCM25Concrete aggregate                        | 3704 |
| full repository                                | 3785 |
+------------------------------------------------+------+
```

All twelve audited declarations depend exactly on
`[propext, Classical.choice, Quot.sound]`.  The source placeholder scan finds
no `sorry`, `admit`, or `sorryAx` proof term.  The full build succeeds; RH
remains open for the analytic reasons listed above.
