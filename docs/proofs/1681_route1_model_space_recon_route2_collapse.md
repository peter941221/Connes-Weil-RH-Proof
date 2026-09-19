# 1681 — Route-1 recon: the trace formula is two-sided (de Branges), not model-space; route 2 collapses into route 1

Date: 2026-09-19.

Status: analysis record (paper level, no Lean, no rig).  Deliverables:
(1) the model-space recon of the uniform-bound estimate — the trace
formula survives for non-inner symbols ONLY in a two-sided form, and the
one calibration point shows no inner free lunch anywhere on the λ-line;
(2) route 2 (the (b1) Titchmarsh skeleton) is not an independent
program — it is route 1's vanishing-side shadow.  No estimate is proved
and RH is not claimed.

## 1. The question route 1 answers

1680 fixed the target exactly: produce

```text
B(n) = tr( 1_ann · C R₀ C† · 1_ann )   ≤   B,   uniform in n,
```

with `C` the convolution by the compact test `g*` and `R₀ = E ∧ Q` the
carrier (meet) projection.  The question was whether the MP model-space
framework — which owns the carrier's NONEMPTINESS criteria (1631/1632
checklist) — also owns a TRACE formula for it.

## 2. Recon verdict

### 2.1 For inner symbols the trace formula exists and is classical

If the carrier were a model space `K_Θ² = H² ⊖ ΘH²` with `Θ` INNER, then
over a carrier ONB

```text
∑_i ‖C J e_i‖²  =  tr( P_Θ M_|ĝ|² P_Θ )  =  ∫ |ĝ|² dμ_Θ,
```

with `μ_Θ` the Clark/resonance measure.  Finiteness of that integral is
then a readable spectral condition.

### 2.2 Our symbol is doubly out of that class

```text
+------------------------------------------------------------+
| obstacle      | fact (committed)                           |
+---------------+--------------------------------------------+
| multiplier    | m = Γ_ℝ(1/2−2πiξ)/Γ_ℝ(1/2+2πiξ) has        |
|               | |m(iy)·m(−iy)| = 1 but is MEROMORPHIC,     |
|               | not inner (1629 F40 pole/zero certificate) |
| exponential   | Θ = e^{4πi(logλ)ξ} with logλ < 0 GROWS     |
| factor        | in ℂ₊ (|Θ| = e^{−4πlogλ·y}, y = Im ξ):     |
|               | anti-inner, so e^{h} ∈ L^{p/2}-type inner  |
|               | reductions are out of class (1632 Q2)      |
+---------------+--------------------------------------------+
```

The m≡1 calibration shows this is not a technicality: even with
`m ≡ 1` the exponential factor alone is anti-inner for every λ < 1.
There is NO point on the λ-line where the pair (exponential, multiplier)
is simultaneously inner-safe.  The inner-model-space trace formula is
therefore not a specialization we can recover as a sanity check — the
correct frame must be the TWO-SIDED one:

```text
  [ one-sided H²(ℂ₊) model space ]      [ our object ]
        K_Θ, Θ inner               ⇒    carrier of the de Branges
        Clark measure μ_Θ               pattern (1626/1629 retype):
        ∫ φ dμ_Θ                        W entire, W/A ∈ H²(ℂ₊),
                                        W/B ∈ H²(ℂ₋); the trace
                                        integral runs against the
                                        DISCRETE spectral measure of
                                        the associated canonical
                                        system (zero-type data)
```

This matches the 1632 decision-tree state: the base's live route was
already "an infinite-type witness outside the meromorphic-inner class";
the recon says the SAME replacement is forced at the trace level, not
just the nonemptiness level.

### 2.3 What the two-sided trace formula must price

The committed phase budget (1631, 30 dps) `γ = −2πξlog|ξ| + 2πξ + π/4 +
O(1/ξ)` is the density input of the canonical system; the trace-finiteness
condition becomes square-integrability of `|ĝ|²` against the spectral
measure determined by that density.  This is a genuine RH-content
condition — 1680's no-slack iff guarantees there is no softer substitute.

## 3. Route-2 collapse

The (b1) mechanism — one-sided vanishing, Titchmarsh-type support
arguments — is EXACTLY 1634's reformulation of carrier nonemptiness
(`K ∗ h ≡ 0` on `(−∞, c)`).  A support dichotomy can decide the carrier
empty/nonempty; it cannot produce the MASS `∑ ‖CJ e_i‖²`.  Any
quantitative strengthening of (b1) (how much mass can survive the
one-sided constraint) parametrizes through the same two-sided spectral
measure as §2.3.

Verdict: route 2 is route 1's u-side shadow — keep ONE lane; the
Titchmarsh skeleton survives as a LEMMA inside route 1 (it governs the
vanishing half of the meet), not as a parallel program.

## 4. Next steps

1. Pin the two-sided trace identity in committed vocabulary: name the
   object that plays `P_Θ` (the carrier projection through the de
   Branges W-pattern) and state `∑_i ‖CJ e_i‖² = ∫ |ĝ|² dμ_disc` as a
   paper-level identity with a calibration check against m≡1
   (B = 0 for N ≥ a+R).
2. From the phase budget compute the density of `μ_disc` explicitly
   enough to test finiteness for the committed `g*` — this is where
   1631's `β < 1` / `β < 2` budgets re-enter as integrability slots.
3. Only then: Laguerre obligations 2–4 (front B) in parallel, since the
   carrier basis is the object over which both fronts sum.
