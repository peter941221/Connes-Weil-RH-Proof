# 969 - Wall-A 1.4 `hI` leaf: why the current witness cannot host the Lean bound, and the re-point that can

Date: 2026-08-10.  Status: decisive triage of the single surviving Wall-A leaf
(docs/965/966).  Not a proof; this pins *why* the leaf is stuck and the exact
thing that unblocks it.  RH NOT claimed.

## What we were trying to close

Closing through `Wall14ArchSufficiency.archimedeanTerm_ne_zero_of_lead_pos_and_integral_bound`
the inequality

```
hI : | Re(∫_{y>0} owner.archimedeanIntegrand y) | < (log(4π)+γ) * Re((f★f)(0))
```

at the self-created witness `witnessTest := unitFourierCoreBumpSchwartz`
(`Wall14SelfTestWitness.lean`).  Closing `hI` axiom-clean refutes the healthycarrier SCAL/SCB (docs/965).  Numeric probe (967/968) reads `arch = +2.93`,
`|I|/A = 1.023 < C = 3.108`, headroom ~2.93 — i.e. NOT borderline.

## Finding 1 — the "only 0 ≤ F(y) ≤ A" bound cannot close the middle piece

I hoped naive-crude bounds could replace the pointwise F bound the docs flagged.
Standard Cauchy–Schwarz gives `0 ≤ F(y) ≤ A` for every compact test
(`F(y)=∫f(t)f(y−t)dt`, even real).  Using ONLY that on the middle `[y0,R]`:

```
|I_-| ≤ 2A * ∫_{y0}^{R} 1/(e^y−e^−y) dy
     = 2A * [ ln tanh(R/2) − ln tanh(y0/2) ]
```

At `R=2, y0=0.27`: `≤ 2A*1.736 = 3.47A`, **exceeding C = 3.108A**.  Even together
the bound `|I| ≤ 3.47A + near + 0.545A` is > C.  So the *crude amplitude* bound
is provable but insufficient: the middle integrand only stays small because
`e^{y/2} F(y)` stays close to `A`, which a `0≤F≤A`-only argument cannot see.
The docs' warning stands — the middle genuinely needs a sharper pointwise
lower/upper control on `F(y)` (equivalently `(A−e^{y/2}F(y))/den`).

## Finding 2 — the current chosen witness's F is NOT Lean-readable (opaque base)

The concrete witness `witnessTestSelf = unitFourierCoreBumpSchwartz` is a mathlib
`ContDiffBump (0:ℝ)` with `rIn=1/2, rOut=1`.  Its value is defined through

```
ContDiffBump.toFun  =  (someContDiffBumpBase E).toFun (rOut/rIn) ∘ (rIn⁻¹ • (int − c))
someContDiffBumpBase E := Nonempty.some hb.out
```

`Nonempty.some` is an opaque `Classical.choice`: the pointwise shape of the bump
on the transition `|x| ∈ (1/2,1)` is not definitionally accessible in Lean
(nor is it equal-by-definition to the `smoothTransition` that the numeric probe
used).  Consequence: any pointwise estimate on `F(y)` needed by Finding 1
either (a) imports `ContDiffBumpBase.ofInnerProductSpace` internally (the big
exact-definition battle docs/966 warned about) or (b) cannot be stated.  The
math is real (the inner product instance IS `smoothTransition((R−‖x‖)/(R−1))`)
but Lean has no access through the chosen bundled path.

## Verdict

The `hI` leaf as currently written (witness = opaque `unitFourierCoreBump`)
cannot be closed axiom-clean in Lean without an `import`-level exact-definition
fight over `someContDiffBumpBase`.  The robust closing path (docs/966
recommendation, now confirmed REQUIRED) is:

**re-point `witnessTest` to an explicit, author-controlled compact bump**
whose `F(y)=∫f(t)f(y−t)` pointwise shape is fully explicit and bounded, e.g.
`f = exp(−1/(1−x²))` on `(−1,1)` (else 0), with stated compact support and a
provable lower control on `F(y)`.

That re-point is the single blocking change.  Once it lands:
add plain-vanilla `CauchySchwarz`ish and/or monotone bounds for the new
explicit `F`, split as in 966, then Closing the resulting `|I| < C·A` into the
already-closed sufficiency.  The sufficiency/refutation/reduction layers are
never touched again (they are closed bytes, docs/965).

## Concrete next-session target (after re-point)

1. `(f★f)(0) = ‖f‖² ≥ A0 > 0` (from `f ≥ m > 0` on `[-1/2,1/2]`).
2. `0 ≤ F(y) ≤ A` (Cauchy–Schwarz; Lean-addable) — enough for the pieces
   except middle.
3. middle `[y0,R]`: prove `e^{y/2}F(y) ≥ A·e^{−(R−y)/2}`-type pointwise enough
   that `∫|A−e^{y/2}F|/den` stays ≤ ~1 centile (target `≤2.2A` with headroom).
4. tail exact closed form; near removable limit; assemble.

Cross refs: docs/965 (dead verdict), 966 (plan), 964 (reduction), 958 (arch probe),
968 (per-piece split); `Dev/Wall14*`.  RH NOT claimed.

