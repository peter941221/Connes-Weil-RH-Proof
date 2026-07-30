# Proof 648: uniform alternating primitives

## Result

Proof 648 identifies the exact quantitative condition left open by Proof 647.
For a contraction `U` and a complete coupled target `C`, define

```text
P_N(U) = sum_(0 <= k < N) (-U)^k.
```

Lean proves both telescope orientations:

```text
(I + U) P_N(U) = I - (-U)^N,
C P_N(U) (I + U) = C - C(-U)^N.
```

Assume the terminal orbit decays on every ambient input:

```text
C(-U)^N u -> 0.
```

Then one uniform bound

```text
sup_N ||C P_N(U)|| <= M
```

implies the same-vector estimate

```text
||C u|| <= M ||(I + U)u||.
```

Douglas factorization therefore constructs a bounded quotient

```text
C = Q(I + U),
||Q|| <= M.
```

Conversely, if `C = Q(I + U)` and `||U|| <= 1`, then

```text
C P_N(U) = Q(I - (-U)^N),
sup_N ||C P_N(U)|| <= 2||Q||.
```

Thus a bounded antiresonant quotient exists exactly when the canonical
alternating primitives are uniformly bounded, up to the factor two in the
reverse norm estimate.

## Actual finite-S owner

At unit Sonin scale, `U` is the positive prime-log translation and `C` is the
complete coupled ambient target from Proof 646. Proof 648 strengthens Proof
647's terminal theorem from suffix-frame inputs to every ambient vector:

```text
C_(p,S)(-U_(log p))^N u -> 0
```

for every fixed `u` in the whole finite-S carrier.

The actual loss includes the positive scale `s_p`:

```text
L_p^dagger = s_p(I + U_(log p)).
```

The canonical scaled readouts are

```text
H_(p,S,N) = s_p^(-1) C_(p,S) P_N(U_(log p)).
```

For a fixed `(p,S)`, Lean proves

```text
sup_N ||H_(p,S,N)|| < infinity
  <->
exists Q_(p,S), C_(p,S) = Q_(p,S) L_p^dagger.
```

The forward construction preserves the supplied bound. The reverse
construction costs at most a factor two. Restricting the ambient quotient
to `newFrame_S` gives the raw Bone 1 readout with no further norm loss.

## Why this is not Bone 1

The theorem is an exact criterion, not a proof of its premise. Compactness
only supplies the terminal statement

```text
C(-U)^N u -> 0.
```

It does not bound the partial sums

```text
C P_N(U)u = sum_(k<N) C(-U)^k u.
```

These are different assertions: terms can tend to zero while their partial
sums remain unbounded. Proof 648 also works one fixed `(p,S)` at a time;
Bone 1 needs one constant shared by every route-valid step.

```text
+------------------------------------------------------+------------------+
| layer                                                | status           |
+------------------------------------------------------+------------------+
| two-sided alternating telescope                     | proved           |
| ambient terminal decay for every fixed input        | proved           |
| uniform primitive bound -> Douglas quotient         | proved           |
| quotient -> primitive bound with factor two         | proved           |
| fixed-step equivalence for the actual owner         | proved           |
| restricted raw Bone 1 readout from that premise     | proved           |
| uniform primitive bound for one actual step         | open             |
| one bound across all route-valid steps              | open             |
| Bone 1 / Gate 3U / finite-S sign / Burnol / RH       | open             |
+------------------------------------------------------+------------------+
```

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorUniformAlternatingPrimitive.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorUniformAlternatingPrimitiveAudit.lean
```

## Verification

The Ubuntu-24.04 WSL2 ext4 focused audit passed under the shared Lake lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| focused fourteen-declaration audit   |  3419 | PASS   |
+--------------------------------------+-------+--------+
```

All fourteen audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
