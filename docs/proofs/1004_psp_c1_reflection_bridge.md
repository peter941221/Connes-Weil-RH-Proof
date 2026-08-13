# 1004 - PSP C1: the reflection bridge R o P+ o R = P- (status + exact reduction)

Status: CLOSED (2026-08-12). The full reflection bridge `R o P+ o R = P-` is now
proved axiom-clean in `CCM24PaleyWienerSpectral.lean`. C1a (coefficient mirror),
C1b (`R o M+ = M- o R`), C1c (`F.R = R.F`, L2-Fourier via Schwartz-density
extension), and the C1 assembly are all green (WSL flock `lake build` 2964 jobs,
#print axioms=[propext, Classical.choice, Quot.sound], 0 sorry). Remaining: H3
(the scattering Toeplitz-kernel / prolate witness); 998/999 still blocked. RH not claimed. No sorry /
axiom added.

## Why C1 matters

docs/1002 §2 needs `\u03c8(xi) = \u03c6(-xi)` (reflection flipping H- to H+). In the
spectral layer, that reflection is the `L2` isometry
`ccm24LogSpectralReflectionLinearIsometry` (call it `R`), and H+ / H- are
`ker P-` / `ker P+` (H2b). For `u in ker P+` (H-), membership in H+ of `R u`
reduces to `P- (R u) = 0`. The identity that makes `R` conjugate P+ to P- is

    R o (ccm24PositiveFrequencyProjection) o R = ccm24NegativeFrequencyProjection.

## Decomposition of C1

C1 := `R o P+ o R = P-`, with

    P+ = F.symm o (1_{+} * . ) o F,   P- = F.symm o (1_{-} * . ) o F,
    F = Lp.fourierTransform_l_i (the L2 Fourier isometry),
    R = reflection `f(x) -> f(-x)`.

- (C1a) [CLOSED, committed] the coefficient mirror:
    `ccm24FreqPositiveHalf_mirror_pointwise : 1_{+}(-x) = 1_{-}(x)` off `{0}`,
    `ccm24ae_ne_zero_volume : forall-a.e.-ae x != 0`,
    `ccm24FreqHalf_mirror_ae : (fun xi => 1_{+}(-xi)) = a.e. 1_{-}`.
  These are the `R o M+ = M- o R` (multiplier conjugation) plant.
  Axiom `#print axioms` = [propext, Classical.choice, Quot.sound].

- (C1b) [CLOSED, axiom-clean] `R o M+ = M- o R` for the frequency multipliers.
  The `ae`-coefficient bookkeeping is isolated: after `rw [houter]` the goal is
  `(R (M+ u)) xi = (M- (R u)) xi`, and the six `ae`-facts give
      (M+u)(-xi) = 1_{+}(-xi) * u(-xi)      [via quasiMeasurePreserve.ae_eq of
                                             Lp.coeffsm_lsmul, see below]
      (M- (R u)) xi = 1_{-}(xi) * (R u)(xi) , (R u)(xi) = u(-xi),
      and 1_{+}(-xi) = 1_{-}(xi)  [C1a].  Both reduce to `1_{-}(xi) * u(-xi)`.
  The only friction in Lean is the ` (↑↑(...) o Neg.neg)` coercion inside a
  `change` after pulling `(-xi) -> xi`; use either explicit typing
  `((ccmMul .. u : cc20GlobalLogCrossingL2) : Real -> Complex) (-x)` or
  `rw [houter]; congr / rw [hPM.at]`. The `ae_eq` used is
  `(Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq`.

- (C1c) [CLOSED, axiom-clean] `F.R = R.F` for the L2 Fourier isometry themselves.
  `F = Lp.fourierTransform_l_i` is defined by
  `(fourierEquiv Complex (SchwartzMap R C)).extendOfIsometry ...`
  and has a coeff-based density `SchwartzMap.denseRange_toLpCLM ` plus
  `SchwartzMap.toLp_fourier_eq`. A proof needs: (i) `R` is a bounded L2 map with
  Schwartz-level reflection `R_fun j = j (-.) ; (ii) the Schwartz-level
  Fourier reflection lemma `fourierInv_eq_fourier_comp_neg` /
  `fourier_comp_linearIsometry` gives `Fourier (j (-)) = (Fourier j) -` ; (iii)
  extend to L2 by continuity (both `F.R` and `R.F` are continuous and agree on
  a dense `toLp` subset). This is a small but genuinely new extension proof; it
  is the only remaining real content of C1.

- (C1-asm) [CLOSED, axiom-clean] compose (C1b) + (C1c):
    `R P+ R = R (F.symm M+ F) R
       = F.symm (R M+ R) F`   (using F.R = R.F and the involutions of F, R)
       = F.symm M- F = P-,
  where `R M+ R = M-` is (C1b).  This has the standard `equiv`-conjugation
  shape.

## Subspace consequence (H2b bridge, after C1)

`u in H- (= ker P+)` implies `R u in H+ (= ker P-)`, since
   P- (R u) = R (P+ (R (R u))) = R (P+ u) = 0.
This is the docs/1002 `psi = phi(- )` symbol bridge. Still only the 'bridge';
a nonzero phi still requires H3 (a Toeplitz-kernel witness), which is untouched here.

## Where everything stands

- Built + audited axiom-clean: C1a (commit 31a05fd), then C1b, C1c, C1-asm
  (this session) — the full bridge `R o P+ o R = P-` is now closed.
- Module `CCM24PaleyWienerSpectral` builds green 2964 jobs; #print axioms
  [propext, Classical.choice, Quot.sound]; 0 sorry in the added block.
- Route crux still OPEN: H3 (Toeplitz-kernel/prolate witness for `m`), 998/999 still blocked,
  RH not claimed.
