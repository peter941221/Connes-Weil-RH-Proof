# Record 1331 — Carrier structure reconnaissance: the head window cannot falsify `hcolumn`

Date: 2026-09-11.
Status: READ-ONLY paper reconnaissance closing out the record 1330
falsification branch (i). No Lean brick, no numerics, no preregistered gate is
opened here; per the house record-first rule the analysis is committed before
any further work depends on it. No vanishing, no `qw` sign, no `SourceRH`, no
RH claim. RH is not claimed.

## 1. The committed HT model (verbatim)

`CCM24HardyTitchmarsh.lean` defines the concrete transform and the carrier:

```lean
-- :340-345  spectral readback:  FT (HT u) = M_phi (R (FT u)),  i.e.
--           (HT u)^ (xi) = phi(xi) * u^(-xi)
theorem ccm24ArchimedeanHardyTitchmarsh_fourier_readback (u) :
    Lp.fourierTransform (ccm24ArchimedeanHardyTitchmarsh u) =
      ccm24ArchimedeanScatteringMultiplier
        (ccm24LogSpectralReflection (Lp.fourierTransform u))

-- :104-112  the phase, |phi| = 1:   phi(xi) = Gamma_R(1/2 - i.2pi.xi) / conj(Gamma_R(1/2 - i.2pi.xi))
noncomputable def ccm24ArchimedeanScatteringPhase (xi : ℝ) : ℂ :=
  ccm24ArchimedeanFactor xi / conj (ccm24ArchimedeanFactor xi)
theorem norm_ccm24ArchimedeanScatteringPhase (xi : ℝ) :
    ‖ccm24ArchimedeanScatteringPhase xi‖ = 1

-- :376-381  the carrier:  TWO support conditions on the SAME log-L2 space
noncomputable def ccm24ArchimedeanSoninClosedSubspace (lambda) :=
  ccm24LogRadialSupportClosedSubspace lambda ⊓
    ccm24ArchimedeanFourierSupportClosedSubspace lambda
```

and `CCM24FiniteSFixedSourcePolar.lean` fixes the range geometry:
`parameterizedSoninPolarFrame_adjoint_comp_self` (frame†∘frame = id, so the
frame is an isometry and `P_S := frame∘frame†` is the orthogonal projection
onto `range frame`), plus `parameterizedSoninPolarFrame_range` (range =
finite-Euler transport of the Sonin subspace).

## 2. The two-sided Hardy form (paper, classical)

Fix Mathlib's Fourier convention `exp (-2*pi*I*x*xi)`. By the Paley–Wiener
half-plane equivalence (`f = 0` a.e. on `(-oo, a)` ⇔ `f^` is the boundary
value of an `H^2` function on the LOWER half-plane, times the character
`xi ↦ exp (-2*pi*I*a*xi)`), the carrier, conjugated by the unitary Fourier
transform and the reflections/characters (all unitary, none affecting the
question below), is exactly

```text
W := { w in H^2(C+) :  phi * w  in H^2(C-) },
phi(z) := Gamma_R(1/2 - 2*pi*I*z) / Gamma_R(1/2 + 2*pi*I*z),   |phi| = 1 on RR.
```

Key structural facts, each standard:

1. `phi` is meromorphic on all of `CC` (quotient of entire-in-argument `Gamma_R`
   factors); its poles are the zeros of the denominator and vice versa,
   interlaced on the imaginary axis at `Im z = +-(m + 1/2)/(2*pi)`, `m >= 0`
   (Mathlib's `Gamma_R` has poles at all non-positive integers). `phi` is
   ANALYTIC AND NONVANISHING in the interior of each half-plane.
2. If `w in H^2(C+)` and `phi*w in H^2(C-)`, then `w` is entire: analytic in
   `CC+` by assumption; in `CC-`, `w = (phi*w)/phi` is a quotient of two
   functions analytic in `CC-` with `phi` nonvanishing there.
3. Stirling on `|Gamma_R(sigma + 2*pi*I*xi)| ~ (2*pi|xi|)^(sigma/2 - 1/4)` (the
   `e^(-pi|xi|/2)` factors cancel between numerator and denominator) gives the
   horizontal-line weight: for `sigma = 2*pi*eta > 0`,

   ```text
   |phi(x - I*eta)| ~ (1 + |x|)^(-2*pi*eta),  uniformly in x,
   ```

   so `w` is `L^2` on the line `Im = -eta` with decaying weight
   `(1+|x|)^(+4*pi*eta)` and `H^2`-uniform on the upper side.
4. Three-lines/strip interpolation then puts ALL polynomial moments of the
   boundary value into `L^2`: `w* in L^2((1+|xi|)^{2s} dxi)` for every `s`.
   Returning to the `x`-picture: every carrier element `u` lies in every
   Sobolev space `H^s` on the interior of its support, so the carrier is a
   Hilbert space of CONTINUOUS functions with bounded evaluation:
   an RKHS with a continuous reproducing kernel `K(t, s)` on
   `(log lambda, oo) x (log lambda, oo)`, and

   ```text
   |u(t)|^2 <= K(t,t) * ||u||^2,    sup_{t in head} K(t,t) < oo.
   ```

5. The scale `lambda` enters ONLY through the character
   `xi ↦ exp(-2*pi*I*(log lambda)*xi)`: `W` (hence `K` up to that character)
   is the SAME space for all `lambda` — the model is scale-covariant.

References for the classical chain: Paley–Wiener half-plane theorem and
three-lines (Stein–Weiss, *Introduction to Fourier Analysis on Euclidean
Spaces*, Ch. 4; Reed–Simon II, Thm X.15); the space itself is the
Sonin/Weil model space and its de Branges (Hermite–Biehler) form is the
subject of de Branges, *Hilbert Spaces of Entire Functions* (1968) — in that
language `W` is the model/Toeplitz kernel `ker T_phi`, which for this
meromorphic `|phi| = 1` symbol is NONTRIVIAL (Weil's own explicit-formula
test functions, products `Lambda(x+a)Lambda(x+b)`, are classical nonzero
witnesses in the `x`-picture: "Sur les 'formules explicites'", Parts I–II,
1952).

## 3. Consequence for the record 1330 dichotomy

Record 1330 §3 registered: `(i)` non-compact head window ⇒ `¬hcolumn`, or
`(ii)` zero/finite head-window mass ⇒ criterion silent. The §2 chain decides
the branch in the classical model:

```text
+--------------------------------------------------------------+
|  head window [log lambda, log lambda + log p)                |
|  = COMPACT interval inside the open support;                 |
|  M_head|carrier  is not merely compact but HILBERT-SCHMIDT:  |
|                                                              |
|     sum_i ||radialComplement(headWindow) e_i||^2             |
|        = integral over head of K(t,t) dt                     |
|        <= (log p) * sup_head K(t,t)  < infinity.             |
|                                                              |
|  => BRANCH (i) IS UNREACHABLE in the committed HT model.     |
|  => The head window NEVER falsifies hcolumn.                 |
+--------------------------------------------------------------+
```

So the 1330 brick stays true and sharp but its falsification arm is dead:
the whole life-or-death of `hcolumn` remains exactly what record 1329 §8
registered — the IDENTITY-part divergence must be cancelled on the
INTERIOR/TAIL `[log lambda + log p, oo)` (infinite measure), i.e. the
carrier must asymptotically `p`-antiperiodize, and the registered necessary
condition (the vanishing-exclusion counting function must dominate the
non-antiperiodic mode count at every scale) is unchanged. The RKHS structure
also says WHERE the mass goes: bounded evaluation with a fixed scale means
the head-window energy is `O(log p)` with a scale-uniform constant, so the
`hcolumn` series, if it converges, converges for TAIL reasons only.

## 4. Registered formal gaps (none authorized by this record)

```text
G1  carrier nondegeneracy: W != {0}  (1329 rank-gap law; the Weil
    Lambda-Lambda witnesses are a classical, unformalized argument)
G2  the two-sided-Hardy => entire => moments => RKHS chain of section 2
    (Paley-Wiener strip package; multi-record analytic formalization)
G3  kernel/trace identification sum_i ||M_head e_i||^2
    = integral_head K(t,t) dt for P_S (needs a formal reproducing-kernel
    story for P_S; repo trace machinery exists only for the crossing
    kernels, not for P_S itself)
```

A formal attack on any of these is a NEW preregistration and is not
authorized here. Cost/benefit as of this record: G2 is a package build, not
a brick; and because section 3 shows the head-window criterion can never
fire, opening G2 buys NO falsification power for `hcolumn` — its only
consumers would be (a) proving `P_S`-tail trace-class facts directly
(= attacking the 1329 necessary condition, which needs the ZERO-side input
that does not exist yet in-repo) or (b) carrier nondegeneracy (G1) as a
route-legitimacy check. Verdict: HOLD the radial leg; the decision-relevant
question for G8 P1 is now singular — tail antiperiodization capacity — and
no formal or numerical instrument in the repo reaches it today.

## 5. What this record changes on the map

- 1330's dichotomy: branch (i) CLOSED (classically); branch (ii)-style
  silence is the standing expectation.
- The "cheap decisive test" role assigned to the head window in 1330 §2 is
  discharged: the test passes and cannot fail.
- Route-A's remaining falsification surface = 1329 §8 necessary condition,
  unchanged and now known to be the ONLY one.

RH is not claimed.
