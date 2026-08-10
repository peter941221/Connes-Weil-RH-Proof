# 941 - Verified Gamma-argument bricks (axiom-clean)

Date: 2026-08-10. Status: first verified bricks of the Weierstrass log-Gamma
argument formalization. RH NOT claimed.

## 1. What is verified (WSL green, axiom-clean)

`Dev/GammaArgBricks.lean` (new) proves, all with `#print axioms =
[propext, Complex.Classical.choice, Quot.sound]` and 0 sorry:

  * `arg_one_add_I_mul (hx : 0 <= x) : arg(1 + I*x) = Real.arctan x`
      - route: `re (1+I x) = 1 > 0` => `|arg| < pi/2` (`abs_arg_lt_pi_div_two_iff`);
        `tan (arg z) = x/1` (`Complex.tan_arg`); tan injective on (-pi/2,pi/2)
        (`tan_inj_of_lt_of_lt_pi_div_two`) with `tan (arctan x) = x`.
  * `arg_one_add_I_half : arg(1 + I/2) = arctan(1/2)`.
  * `arg_one_add_I_div_two_nat (n, 0<n) : arg(1 + I/(2n)) = arctan(1/(2n))`.

These are exactly the factor-phase identities used by the Weierstrass log-Gamma
argument at the finite-S base point `1 + I/2`
(`arg(Gamma(1+I/2)) = -gamma/2 - atan(1/2) + Sum_n[1/(2n) - atan(1/(2(n+1)))]`).
`Complex` does provide `arg` additivity for products via
`arg_mul_coe_angle` (Real.Angle), so the product-log channel is also available.

## 2. Numeric certification of the target (Cross-check)
Python `scipy.special.gamma(1+0.5j)` => `arg = -0.2440582989`;
the Weierstrass formula with S at N=1e6 => `-0.2440587989` (diff ~5e-7);
`|arg| < pi/8 = 0.392699` with margin ~0.1486. `tan(pi/8) = sqrt2-1`, matching
the A3 cone in `Finite3SignReduction`.

## 3. What remains (open analytic leaf)
Connect `arg(Gamma(1+I/2))` to the series (Weierstrass log-Gamma identity at the
point), then bound the series via `SSeriesSandwich`/`PhaseGateSandwich`/`ArctanCert`.
That step (`(Gamma (1 + I/2)).arg = D`) is still a large in-repo real-analysis
formalization. Done, the finite-S sign closes (`gammaSign_at_one` in
`Dev/GammaArgLeaf.lean`). Still no RH (the exit is RH-equivalent).

## 4. Verified: Finset product-argument additivity (this turn)

`Dev/GammaArgSum.lean` (new, axiom-clean, 0 sorry) proves the structural backbone
`arg_prod_coe_angle : ((Finset.prod t f).arg : Real.Angle) = Finset.sum t (fun i => (f i).arg)`
for any `t : Finset Nat` with every `f i != 0` (via `arg_mul_coe_angle`).
This turns the Weierstrass factor args (`GammaArgBricks`) into a summed series:
`arg( prod_n (1 + I/(2n))^-1 e^{I/(2n)} ) = Sum_n ( 1/(2n) term - atan(1/(2n)) )`
at the `Real.Angle` level - exactly the structural backbone of
`arg(Gamma(1+I/2)) = -gamma/2 - atan(1/2) + S`.


## 5. Verified: Gamma-shape arg bricks (this turn, Dev/GammaArgProd.lean)
`Dev/GammaArgProd.lean` (new, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry,
WSL green, 1978 jobs) proves the factor-level spine matching the actual Weylstrass Gamma
factor at z = 1 + I/2:

  * `arg_exp_mul_I_angle : (arg(e^{theta*I}) : Real.Angle) = theta`  (via `arg_exp_mul_I`
    + `Real.Angle.coe_toIocMod`; the pi branch is absorbed by the 2*pi quotient).
  * `arg_factor_coe_angle (hx) : (arg( e^{theta*I} / (1+I*x) ) : Real.Angle) = theta - atan x`.
  * `arg_factor_half : arg(e^{(1/2) I}/(1 + I/2)) = 1/2 - atan(1/2)`.
  * `arg_add_mul_I (hx : 0 < x) : (arg(x + I*y)) = Real.arctan (y/x)`
      general vector-phase identity; exactly the re/im plane for `1 + z/n`.
  * `arg_exp_add_mul_I_angle : (arg(e^{r + I*s}) : Real.Angle) = s`
      gives the exponential half `e^{-z/n} -> -1/(2n)`.
  * `arg_gamma_imag (u, 0<u) : arg((u+1)/u + I/(2u)) = atan(1/(2u+2))`
      the `S`-series summand, `u = n`.
  * `arg_exp_neg_z_div_n (u) : (arg(e^{-1/u + I*(-1/(2u))}) : Real.Angle) = -1/(2u)`
      the `-1/(2n)` exp half that sums to the `SSeriesSandwich.S2` term.

Relation to the closed wheel: `GammaArgProd` = single-factor/exp arg additivity;
`GammaArgSum.arg_prod_coe_angle` = finite-product arg additivity. This is the finite
partial-product preimage of `SSeriesSandwich.S_eq_S2_add_atan_half`
(`S = tsum S2 + atan(1/2)`). The remaining open leaf (unchanged, docs 940):
`arg(Gamma(1+I/2)) = D` (Weylstrass infinite log-Gamma identity + tail), which when
closed feeds `gammaSign_at_one`; still RH-equivalent, no RH claim.

## 6. Verified: finite Weierstrass product-argument closure (this turn)

`Dev/GammaArgSum.lean` gained two generalisation/support lemmas and
`Dev/GammaArgProd.lean` gained the finite-product summation, all WSL green and
`#print axioms = [propext, Classical.choice, Quot.sound]`, 0 sorry:

  * `arg_prod_coe_angle` was generalised from `Finset Nat` to `Finset α`
      (arbitrary index type) so the Weierstrass factor product can be indexed
      over real scales; proof unchanged (generic `Finset.induction_on`).
  * `real_sum_coe_angle (t : Finset α) (r : α → ℝ)` :
      the real-to-`Real.Angle` coercion distributes over a finite sum
      (`↑(∑ r) = ∑ i, ↑(r i)`, via `Finset` induction and `Real.Angle.coe_add`).
  * `weylFactorIm_nonzero` / `weylFactor_ne_zero (u, 0<u)` :
      the `1 + z/n` factor (and hence a full Weierstrass factor) is non-zero.
  * `weylArgNum (u)` : the per-factor argument value `-1/(2u) + atan(1/(2(u+1)))`.
  * `arg_weylFactor_prod_coe_angle (t : Finset ℝ) (ht : ∀ i ∈ t, 0 < i)` :
      `(arg(∏ i∈t weylFactor i) : Real.Angle) = ∑ i∈t (weylArgNum i : Real.Angle)`.
      This is the finite partial-product preimage of the summed series, off the
      single-factor `arg_weylFactor` and the product-additivity backbone.

The open leaf is unchanged and self-contained: connect the infinite Weylstrass
partial-product limit to `arg(Γ(1 + I/2))` (docs/940) — a multi-session
in-repo real-analysis formalization. When closed it feeds `gammaSign_at_one`;
still RH-equivalent, no RH claim.

## 7. Verified: Gamma-Weierstrass partial-sum bridge (this turn)
`Dev/GammaWeierstrassSum.lean` (new, axiom-clean [propext, Classical.choice,
Quot.sound], 0 sorry, WSL green 2641 jobs) ties the finite product-angle spine to
the closed `S`-series:
  * `weylArgNum_eq_neg_a (n)` : `weylArgNum(n+1) = -SSandwich.a n`
    (the per-factor argument equals the negative `a`-series term).
  * `weylArgNum_range_eq_neg_sum (N)` :
    `sum_{n<N} weylArgNum(n+1) = -sum_{n<N} SSandwich.a n`.
Combined with `SSeriesSandwich` (`1/2 <= S <= 1/2+1/32`), the finite product-angle
partial sum is pinned to `[-1/2-1/32, -1/2]` (as `N -> +inf`), i.e. the minus-log-Gamma
phase window. The Gamma-side hinge (`arg(Gamma(1+I/2)) = -gamma/2 - atan(1/2) + S`,
connecting `Complex.Gamma`'s integral to this finite/product series) remains the only
open leaf (docs/940): mathlib has no Weierstrass product for Complex.Gamma, so this
needs a self-contained in-repo log-Gamma identity.

## 8. Verified: hasSum of the Weierstrass phase series (this turn)
`Dev/GammaWeierstrassSum.lean` now also proves, axiom-clean
`[propext, Classical.choice, Quot.sound]`, 0 sorry (WSL green):
  * `hasSum_weylArgNum` : `HasSum (fun n => weylArgNum(n+1)) (-SSandwich.S)`.
This is the convergent series side of the Weierstrass log-Gamma phase identity
(`arg(Gamma(1+I/2)) = -gamma/2 - atan(1/2) + S`). The finite partial sums were
already tied to `-a`; this lifts the whole sequence to a `HasSum` at `-S`, so the
series side is fully pinned. The remaining leaf is connecting `Complex.Gamma`'s
integral to this series (mathlib has no Weierstrass product for Complex.Gamma) -
the open multi-session analytic hinge (docs/940). RH not claimed.

## 9. Verified: numeric bracket on the phase partial sum (this turn)
`Dev/GammaWeierstrassSum.lean` adds `negS_bounds` (axiom-clean, WSL green):
  * `negS_bounds` : `-(1/2+1/32) <= -SSandwich.S <-> SSandwich.S <= -1/2`,
    i.e. `-S in [-0.53125, -0.5]`, from the closed S-series sandwich.
Combined with `hasSum` the phase partial-sum is fully pinned; the only remaining
hinge to `arg(Gamma(1+I/2)) = -gamma/2 - atan(1/2) + S` is connecting Complex.Gamma's
integral to this series (no Weierstrass product in mathlib) - docs/940. RH not claimed.
