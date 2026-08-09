# 914 (Door B, closure) — build-verified: the four Hilbert bases instantiate, the trace-class witness closes at `(1,1)`

Status: build-verified (probe `ConnesWeilRH/Dev/A24RetypeGateSeam914Closure.lean`,
WSL, `lake build` green, `#print axioms traceClass_witness_at_window` =
`[propext, Classical.choice, Quot.sound]`). No RH claimed.

## What this closes

`docs/proofs/914b_retype_seam_buildverified.md` named one residual gap as "still
unbuilt": the seam theorem `seam_traceClass_family` is parameterized over the
four Hilbert bases, so it did not yet assert a single satisfiable witness at one
fixed window. This file closes that by instantiating each basis from
`exists_hilbertBasis` (complete complex `L^2`) and packing the trace-class-along
conjunct into one theorem at the fixed window `(1,1)`.

| item | contents |
| -- | -- |
| `traceClass_witness_at_window` | `∃ nw pw ow gw` (the four `Set`s) `∃ negB posB outB globB` (their `HilbertBasis`es), `IsTraceClassAlong globB (signedBoundaryOperator gateTest 1 1 negB posB outB globB)` |
| Witness source | `exists_hilbertBasis` on each complete `L^2` carrier, then `seam_traceClass_family` at `(1,1)` |
| Axiom audit | `[propext, Classical.choice, Quot.sound]` — no `sorry`, no new `axiom` |

The one genuinely-unbuilt seam of 914/914b is now exactly the two-step narrow:
`gateTest` is a `CompactLogTest`; the route's archimedean `Test` is the re-type
(`ConcreteTest = TestFunction`), and the OBJECTS-layer `sourceHilbertSchmidtGate`
remains filled from `…Root` axioms rather than this CompactLog witness. That
carrier re-type still stands as the next finite act; it is not performed here.

## Scope / honesty

- No RH claimed. Zero `sorry`. No new `axiom`.
- Pure instantiation of the seam's already-axiom-clean theorem; new content is
  only the `exists_hilbertBasis` completeness witnesses.
- The residual handle moves from "the trace-class conjunct has no concrete
  basis" to "the route's archimedean `Test` (`TestFunction`) needs the
  CompactLog-carrier witness re-typed onto it, and the OBJECTS gate field needs
  to read from that re-typed carrier."