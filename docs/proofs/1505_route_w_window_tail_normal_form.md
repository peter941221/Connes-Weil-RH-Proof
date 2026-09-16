# 1505 — Route W as a window/tail decomposition normal form

**Status: FORMAL (abstract layer).** New leaf
[`C1G8R3RouteWWindowTailNormalForm.lean`](../../ConnesWeilRH/Dev/C1G8R3RouteWWindowTailNormalForm.lean)
(+ paired audit). Record 1503 §3 registered route W (window strip) as the
formalizable half of the (★) attack; this file isolates the
operator-algebraic core of that registration as machine-checked theorems.
RH is not touched; no estimate is proved.

## What is proved

Full generality — Hilbert spaces `H`, `G`, a Hilbert basis, `T : H →L G`,
and an arbitrary bounded `P : H →L H` (no idempotence, self-adjointness, or
contraction needed):

1. **Two-factor split** (private): `‖T u‖² ≤ 2‖T(P u)‖² + 2‖T((id−P) u)‖²`.

2. **Decomposition theorem**
   (`survivorCore_of_windowStrip_of_tailGate`): the column-energy gate for
   `T` follows from the window-strip square-sum for `T ∘L P` plus the SAME
   gate for the tail composition `T ∘L (id − P)`.

3. **Iteration** (`survivorCore_of_twoWindowStrips_of_tailGate`): with a
   second window `Q` applied to the tail, the gate for `T` follows from the
   two window strips and the composite tail. Finer windows absorb more of
   the operator for free; only the collective tail carries content.

## How this types the attack (record 1503 §3, made precise)

* The **window input is free** for genuine windows: instantiating with the
  record-1495 finite-window mechanism (compact strip kernel), the strip
  square-sum is Hilbert–Schmidt unconditionally. The formal engine for the
  concrete instantiation is `ContinuousKernelHilbertSchmidt.basis_normSq_summable`
  (compact carrier, finite measure) plus the interval restriction
  bookkeeping — the remaining formal cost of route W.
* The **tail input is the open mathematics of route T**: it is literally a
  column-energy gate for `T ∘L (id − P)`, the same family as (★). The
  Hardy-pressure finding (record 1503 §2) applies unchanged — any proof of
  the tail gate must read the phase of the scattering multiplier.
* The **B3 composite window** consumes the same theorem: the boundary legs
  `(I − E) C M_p J` of record 1499 are of the form `T ∘L P` with `P` a
  radial window factor, so per-leg estimates reduce to window strips plus
  a composite tail — with `M_p` kept ambient-side (record 1491 guard,
  already committed as
  `C1G8P1SourceProlatePullbackZero`).

## Position

The gate (★) for `C J` is now bracketed formally: every window exhaustion
converts it into (finitely many free strip estimates) + (one tail gate of
the same type). The program of route T is therefore not a new species of
problem — it is the minimal irreducible remainder of route W.
