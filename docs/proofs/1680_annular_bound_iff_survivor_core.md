# 1680 — The uniform annular trace bound is EXACTLY the survivor core (iff, machine-checked)

Date: 2026-09-19.

Status: one Lean brick + Audit, all green.  The front-A estimate and the
gate content are now the same proposition by a committed theorem.  No
estimate is proved and RH is not claimed.

## 1. What landed

`Dev/C1G8R3AnnularTraceEquivalence.lean` (+ Audit):

```text
uniformAnnularTraceBound_of_ambientColumnEnergy
    ambient column energy  ⟹  ∃ B, ∀ n ≥ N, Re tr Gram(N,n) ≤ B
uniformAnnularTraceBound_iff_survivorCore
    (∃ B, ∀ n ≥ N, Re tr Gram(N,n) ≤ B)  ↔
    Summable i, ‖sourceCompressedRoot owner λ e_i‖²
```

Chained with 1676 (bound ⟹ core) and 1659 (`g8EndpointGate_iff_survivorCore`:

```text
  ∃ B uniform annular trace bound
    ⟺  survivor-core square-sum  (this brick)
    ⟺  ambient column energy     (this brick, backward)
    ⟺  endpoint gate              (1659)
    ⟺  SourceRH                   (committed chain)
```

The estimate is the gate.  There is no slack: a proof of the bound IS a
proof of the core; a refutation (at any fixed λ with carrier nonempty)
kills the lane.  The bound comes with an EXPLICIT certificate

```text
B = ∑' i, 4 · ‖rootConvolution owner (sourceInclusion λ (e_i))‖²
```

## 2. The backward argument (three lines)

Each annular output column is the difference of two interval projections
of the same ambient column (`sourceRootAnnularOutputWindow`); both
projections `kernelIntervalProjection (-n) n 0` are contractions (they are
`W ∘L W†` with `W` the kernel-interval zero-extension isometry, norm
`‖W‖ = ‖W†‖ ≤ 1`).  Triangle inequality gives

```text
‖annular column e_i‖ ≤ 2 ‖C J e_i‖,
```

squaring (`sq_le_sq₀`), summing with `tsum_le_tsum`, and transporting
through the exact 1669 column-energy identity `tr Gram = ∑ ‖annular
column e_i‖²` gives the bound with `B = 4 ∑' ‖CJ e_i‖²`.  The ambient
summability premise is converted from the core by 1659.

## 3. Consequences for the attack

* Front A's remaining object is now provably irreducible: the ONE Pi
  statement carries the entire front.  No softer sufficient condition can
  exist (any such condition would prove the gate).
* The m≡1 calibration target (B = 0 for N ≥ a+R, 1678) is the degenerate
  certificate `B = 4·∑' 0 = 0` — consistent.
* Route pricing (1681) inherits a no-free-lunch constraint: any route to
  the bound is automatically a route to RH content.

Build: `build-logs/1680_annular_trace_equivalence.log`, footer
"Build completed successfully (3966 jobs)", zero `^error:` lines, zero
`sorryAx`, both theorems on `[propext, Classical.choice, Quot.sound]`.

## 4. Tooling notes (v4.30, portable)

* The carrier `CompleteSpace` instance in
  `C1G8R3SourceCompressedRootKernel.lean` is `noncomputable local` —
  NOT exported.  Every module that writes `(sourceInclusion λ).adjoint`
  must re-declare it (third copy now: kernel, endpoint, equivalence).
* `Summable.mul_left` has explicit-argument order `(a) (hf)`: the dot form
  `hgate.mul_left 4` fills `hf` automatically, the bare-name form needs
  `Summable.mul_left (4 : ℝ) hgate`.  (Also: when `Summable` displays as
  `∃ a, HasSum ...`, dot resolution on the binder can target `Exists` —
  prefer the bare-name call.)
* `sq_le_sq₀` in v4.30 is `a² ≤ b² ↔ a ≤ b`; the small-to-squared
  direction is `.mpr`, not `.mp`.
* `sourceCompressedRoot` unfolds definitionally to the iff's inline
  composition `(J† ∘L C ∘L J)`; a `show`-cast works, but the committed
  pattern is to state hypotheses in the inline form directly.

## 5. Boundary

No uniform bound is proved.  The route-1/route-2 pricing is record 1681.
RH not claimed.
