# Plan: Mellin-product convolution identity for a real source carrier

Date: 2026-08-06 · Status: **plan (computation write-up, before any Lean implementation)** ·
Owner lane: parallel source model → the "new Mellin identity" this session identified as the forced bottom

## Background (one line)

The concrete `convolutionStar = f+g` is additive and cannot satisfy
`NormalizedCC20MellinConvolutionLaw` (`mellin(f✳g)=mellin f · mellin g`);
`not_normalizedCC20MellinConvolutionLaw` (`CC20YoshidaConstruction.lean:2727`) and
`not_...WeilCriterion` (`:2475`, counterexample) prove no in-model reassembly works.
So a **new carrier** whose convolution genuinely multiplies under Mellin is forced.

## Goal

Prove (as a theorem, axiom-clean, no sorries) the Mellin-convolution identity for
the log-coordinate additive convolution on `CompactLogTest`:

```
Goal (MellinProduct):
  ∀ f g : CompactLogTest, ∀ s : ℂ,
    MellinIoi (fun t => (f.convolution g).test (Real.log t)) s      -- (★)
  = MellinIoi (fun t => f.test (Real.log t)) s
  · MellinIoi (fun t => g.test (Real.log t)) s
```

where `MellinF Ioi h s := ∫ t ∈ Ioi 0, t^(s-1) • (h t)` is the project's locally
scoped Mellin on a lifted function `h : ℝ → ℂ`.

`f.convolution g` is the *additive-log* convolution `∫ f(t)·g(x−t) dt`
(`CompactLogConvolution.lean:99`).  Under `t = e^u` this is exactly the
multiplicative convolution `(F ⋆ G)(t) = ∫ F(v) G(t/v) dv/v`, whose Mellin product
law is the harmonic-analysis statement we want.

## The standard proof (blackboard → Lean)

Let `h(u) = f(e^u)`, `k(u)=g(e^u)` (log lifts), and let
`x = log t`, `v = log s`, so `t = e^x`, `s = e^v`.

```
Mellin product side, written by Fubini / change-of-vars u = e^x:

  Mellin(f∘exp) · Mellin(g∘exp)  at s
    = ∫_ℝ ∫_ℝ  e^{x s}·e^{v s}· h(x) k(v)  dx dv
    = ∫_ℝ ( ∫_ℝ h(x) k(z−x) dx ) · e^{z s} dz        (z = x + v, additive conv in log)
    = ∫_ℝ (f.convolution g)(e^z) · e^{z s} dz
    = Mellin of (log-lift of f.convolution g).

So the identity (★) is exactly the additive-Mellin transitivity: the additive-log
convolution synthesized by CompactLogConvolution is conjugate to the
multiplicative Mellin convolution through u ↦ e^u.
```

## mathlib coffee (what already exists to build on)

- `mellin` def: `∫ t in Ioi 0, (t:ℂ)^(s-1) • f t` (`.lake/.../MellinTransform.lean:92`).
- `mellin_comp_rpow` (`:117`): `mellin (fun t => f (t^a)) s = |a|⁻¹•mellin f (s/a)` —
  the log substitution bridge; `mellin_comp_inv` (`:156`).
- `MeasureTheory.convolution` for the additive log conv.
- No Mellin *convolution* theorem exists yet in mathlib (`MellinTransform.lean`
  is single-function only) — this is the genuinely new part.

## Implementation skeleton (Lean, in a new module)

1. **Lift**: `def logLift (f : ℝ → ℂ) (u : ℝ) : ℂ := f (Real.exp u)`.
2. **Scalar identity** (elementary, easy): reduce (★) to equality of the Mellin
   of `fun t => (f.convolution g).test (log t)` against the convolution of the
   lifts under the log change of variables.
3. **Log-sub density theorem**: `∫_Ioi 0 h t^s dt` ↔ `∫_ℝ h(e^u)·(e^u)^s du`
   via `mellin_comp_rpow`/`integral_comp_rpow_Ioi`.
4. **Fubini reassociation** over the additive-log convolution integral.
5. **Close**: for fixed compact `f g`, both sides finite; equality by the
   standard convolution→Mellin transport. Axiom-clean (`[propext, Classical.,
   Quot.sound]`), no sorries.

## Acceptance / verification

- New module builds clean in isolation (WSL mirror, per AGENTS/footguns).
- `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- Statement (★) holds for the concrete `CompactLogTest.convolution`.

## Risks / honest notes

- The exact integral transport (change-of-vars from `Ioi 0` multiplicative to
  `ℝ` log-coordinate) is algebra-heavy in Lean; expect to fight
  `Real.exp`/`Real.log`. Substantial new measure-theory proof load.
- `CompactLogTest` compact support on `ℝ` does NOT give compact support on
  `Ioi 0` under `t = e^u`? It does: `u ↦ f(e^u)` is compactly supported if
  `f` is; convergence is fine.  Good.
- Axiom-clean is a requirement; if convergence of the reassociation is
  non-trivial this may need a `MellinConvergent`-style hypothesis kept as a
  terminating witness (not an axiom).

## Next steps (concrete, sequential)

1. Prove the **database Mellin conversion of the compact-log convolution** (★)
   as the first new theorem (this is the whole identity).
2. Assemble `SourceTestAlgebra`-free "Mellin-carrier" sub-struct carrying this
   identity, satisfying `NormalizedCC20MellinConvolutionLaw`.
3. Wire to the proven Yoshida detector + criterion, replacing the additive
   we-chair.
4. Build + `axiom` audit.

## Owner / author

Research-context plan awaiting your go/no-go on implementing **step 1** (the new
Mellin identity) as the day's first code unit.