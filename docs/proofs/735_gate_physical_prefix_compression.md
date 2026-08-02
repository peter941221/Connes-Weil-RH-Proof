# Proof 735: Gate Physical Prefix Compression

## Result

Proof 735 replaces Proof 734's all-finsets hypothesis by one ordered natural
Hilbert-basis exhaustion.

Let `e_0,e_1,...` be a Hilbert basis of the source Sonin carrier and let

```text
d_S(i)
  = 2 Re <J e_i, W(F_S e_i)>
    + <J e_i, W(P_S e_i)>
```

be Proof 733's complete signed scalar.  Proof 734 accepts

```text
forall finite A, norm(sum_(i in A) d_S(i)) <= C.
```

That premise allows adversarial positive/negative subset selection.  The new
consumer requires only

```text
forall N, norm(sum_(i < N) d_S(i)) <= C.
```

Fixed-family trace legality makes these nested prefixes converge to the
ordinary Gate trace, so Lean proves

```text
forall N, norm(sum_(i < N) d_S(i)) <= C
  -> norm(Tr(GateResponse_S)) <= C.
```

## Finite-Dimensional Owner

The prefix is not left as an informal scalar sum.  Define the literal
`Fin N` compression matrix

```text
M_(S,N)(i,j) = <e_i, GateResponse_S e_j>.
```

The new owner is

```text
T_(S,N) = Matrix.trace(M_(S,N)).
```

Lean proves exactly

```text
T_(S,N) = sum_(i < N) d_S(i).
```

The source-specific theorem obtains fixed-S trace legality from the existing
Hilbert--Schmidt pair data and leaves only

```text
forall N, norm(T_(S,N)) <= C
```

as the analytic premise.

```text
complete physical Gate operator
              |
              | compress to span(e_0,...,e_(N-1))
              v
       Fin N x Fin N matrix
              |
              | ordinary finite matrix trace
              v
  complete signed prefix sum
              |
              | N -> infinity, fixed-S trace legality
              v
       ordinary Gate trace
```

## Why This Is Stronger

An all-finsets bound can select positive and negative diagonal subsets
separately and therefore approaches a uniform total-variation estimate.  That
is stronger than the signed Gate scalar and can erase cancellation across
basis indices.  Ordered prefixes preserve one coherent exhaustion while still
giving a legal limit.

The finite compression is also the right next owner for compact-root support:
all manipulations are finite-dimensional before `N -> infinity`.

## Guard

Proof 735 does not bound the compression traces.  Finite-dimensional trace
cyclicity does not make prefix-boundary leakage disappear, and the forward and
physical coordinates must still remain inside the complete trace.  Gate 3U,
the finite-S sign, Burnol's identity, and `_root_.RiemannHypothesis` remain
open.

## Verification

The source, import-facing audit, and `CCM25Concrete` aggregate batch passed
with `4004/4004` jobs.  The final full-repository acceptance build after
Proofs 735--738 passed with `4087/4087` jobs.  All four audited Proof 735
theorems use exactly `[propext, Classical.choice, Quot.sound]`.  No `sorry`,
`admit`, user axiom, heartbeat increase, recursion-limit increase, overlong
line, or new linter warning was added.
