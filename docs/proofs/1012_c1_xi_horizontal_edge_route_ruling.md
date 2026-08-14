# 1012 — Gate 2 horizontal-edge bottom: route ruling and next attack brick

Status: ROUTE RULING + attack plan (2026-08-14). The finite-height contour
chain is closed (see `1010`); the remaining analytic bottom of Gate 2 is the
horizontal-edge estimate at height `T -> infinity`.

## 1. Where the chain stands

```text
C1XiVerticalFunctional / ContourDecay      CLOSED  (kernel, quartic weight decay)
C1XiFiniteFactor (+ analytic log upgrade)  CLOSED* (*analytic-log build in flight)
C1XiFiniteRegularization / …Cauchy         CLOSED  (dslope remainder, rectangle Cauchy)
C1XiFiniteRectanglePrincipalPart           CLOSED  (rectangle residue readout)
C1XiFiniteHeightRectangle (+Assembly)      CLOSED  (finite spectral sum readout)
C1XiQuantitativeHeight (+tubes, dyadic)    CLOSED  (zero-free height sequence, gap >= 1/(4N))
C1XiQuantitativePrincipalBound            CLOSED  (finite principal part O(9^n) on both tubes)
C1XiHorizontalDecay                       CLOSED  (conditional bound: envelope M * O(T^-4))

OPEN: quantitative xi'/xi growth (or cofactor log-derivative) on the segment
      -> horizontal edges -> rectangle limit -> Gate 2 equality -> RH.
```

## 2. The horizontal-edge decomposition (what remains is exactly one piece)

On a selected zero-free horizontal segment `t = +/-T_n`, decompose the
log-derivative of the completed xi through the same closed-ball factorization
owner (radius `T+2`, center 0):

```text
-x i'/xi  =  [finite principal part]  +  [logDeriv of zero-free cofactor g]
                  |                              |
                  v                              v
         O(9^n) CLOSED (1011)          the single open analytic input
```

The cofactor term is not bounded by any device in the current modules:
- `C1XiAnalyticLog` (build in flight) supplies the same-owner **analytic
  logarithm** `L` of `g` on the open factorization ball,
  `logDeriv g = deriv L`. This is the necessary precondition for any
  Borel-Carathéodory application, and it is owner-preserving
  (`exists_xiClosedBall_factorization_with_analytic_log_on_ball`).
- Borel-Carathéodory (mathlib `Complex.borelCaratheodory`, v4.30,
  `Mathlib/Analysis/Complex/BorelCaratheodory.lean`) then gives

  ```text
  ||L z|| <= 2*M*||z||/(R-||z||) + ||L 0||*(R+||z||)/(R-||z||)
   Re f <= M                                        ^^^^^^^^
  ```
  and hence `|logDeriv g z|` via Cauchy's estimate. `Re L = log |g|` is
  bounded above on the tube from the closed dyadic xi growth
  (`norm_completedRiemannXi_le_exp_on_dyadic_jensen_sphere`)
  minus the computable factor part (tube separation), so `M` is available.
  **The blocking term is `||L 0|| = |log |g(center)||`: it needs a positive
  lower bound of `|g|` at the tube center, i.e. a quantitative minimum
  modulus of xi on the segment. No such bound exists in mathlib v4.30 and
  none follows from the closed maximum-modulus/Jensen pieces.**

Verdict: the minimum-modulus lane is **not classical**. Standard explicit-formula
proofs (Weil/Burnol/Titchmarsh) never bound the horizontal edge through a
minimum modulus; they use the **canonical-product log-derivative identity**

```text
xi'/xi(s) = b + sum over ALL nontrivial zeros rho of ( 1/(s-rho) + 1/rho )
                                            (+ no Gamma term inside completed xi)
```

whose right side is bounded on the segment from zero-density data alone:

- near zeros (`|Im rho - T|` small): count/sep <= O(9^n)  — CLOSED (1011);
- far tail: geometric 3/4 series from the dyadic Jensen shell counts — the
  only missing Lean piece (brick G, below), no new mathematics;
- the identity itself (`xi` global Hadamard product): new analysis + Lean
  build; mathlib v4.30 has no usable finite-order canonical-product theorem
  for a concrete `completedRiemannXi`.

Route decision: pivot the horizontal-edge attack to the canonical-sum
identity lane. Keep `C1XiAnalyticLog` (owner-preserving analytic log is the
foundation of the same decomposition used there), do not build a conditional
min-mod contract on top of it until the canonical-sum identity is ruled out.

## 3. Brick G: global regularized zero-sum (CLOSED 2026-08-14, WSL verified)

`Dev/C1XiGlobalZeroSum.lean` (written and build-verified 2026-08-14 in a
fresh WSL mirror, lean 4.30 / mathlib v4.30). Axiom status
`[propext, Classical.choice, Quot.sound]`, no new axioms — all premises are
closed modules. Two import fixes were needed during verification:
`ConnesWeilRH.Dev.C1SpectralSummability` provides `spectralMultiplicityConstant`
and `spectralHeightMultiplicity_geometric_bound`; `open CC20YoshidaNearZeros`
provides `sourceNontrivialZeroSet`, `dyadicShellIndex` and its lemmas (none of
these are exported by `C1SpectralWeil`, whose own `open`s do not cross files).

```lean
noncomputable def regularizedZeroTerm (s : Complex) (rho : sourceNontrivialZeroSet) : Complex :=
  1 / (s - rho.1) + 1 / rho.1          -- = s / (rho.1 * (s - rho.1))

theorem regularizedZeroSummable (s : Complex) :
    Summable (fun rho : sourceNontrivialZeroSet => regularizedZeroTerm s rho)

theorem regularizedZeroTail_norm_shellSum_le (s : Complex) (n0 : Nat)
    (hs_lt : |s.im| < (2 : Real) ^ n0) :
    (∑' m : Nat, ∑' rho : spectralHeightShell (m + n0 + 1),
      ||regularizedZeroTerm s rho.1||) <=
      4 * (2 * ||s||) * spectralMultiplicityConstant * (3/4)^n0
      -- crude but the route only needs o(16^n)
```

The tail is grouped by the height shells it covers (shells `n0+1` and up =
all zeros with `dyadicShellIndex |Im rho| >= n0 + 1`), so the consumer
combines it with the finite prefix through the same shell partition.

Proof plan (all ingredients closed; module mirrors it):
1. Generalize `summable_of_shifted_geometric_shell_weight_bound` with a free
   finite prefix: `summable_of_shell_weight_tail_bound` — identical proof with
   `rw [← summable_nat_add_iff (f := fun n => ∑' x : shell n, f x) (n0 + 1)]`
   and the geometric constant absorbing the prefix: per-shell bound comes out
   as `K * B * (q/4)^n0 * (q/4)^m` (the `q^n0` mass growth is absorbed by the
   `4^n0` denominator, so the mass hypothesis needs no scaling).
2. Instance with shell = `spectralHeightShell`, weight = multiplicity,
   `K = spectralMultiplicityConstant`, `q = 3` (3 < 4), `B = 2 * ||s||`,
   `n0` chosen freely (summability instance: `dyadicShellIndex |s.im| + 1`).
3. Pointwise bound per `x : shell (m + n0 + 1)`:
   `||term|| <= ||s|| / (||rho|| * ||s - rho||)` via `regularizedZeroTerm_eq_div`
   (field algebra, both denominators nonzero from the height-shell lower
   bound); then `||rho|| >= 2^(m+n0+1)`
   (`pow_succ_le_of_dyadicShellIndex_eq_succ`), and
   `||s-rho|| >= |Im rho - Im s| >= |Im rho| - |Im s| >= 2^(m+n0)` via
   `abs_sub_abs_le_abs_sub` + `pow_le_pow_right₀` on the dyadic bound
   `|s.im| < 2^n0` (with `n0 <= n`), then `div_le_div_of_nonneg_left`.
4. `1 <= (xiMultiplicity rho : Real)` (`xiMultiplicity_pos`) to inflate the
   weight factor; algebra `2^(n+1) * 2^n = 2 * 4^n` closes the instance.
5. Tail value bound: per-shell `<= K * (2 * ||s||) * (3/4)^(m+n0)` (the
   multiplicity mass bound `spectralHeightMultiplicity_geometric_bound`),
   summed by `tsum_le_tsum` against the geometric series
   (`summable_geometric_of_lt_one`, `tsum_geometric_of_lt_one`), giving the
   closed form `4 * (2 * ||s||) * K * (3/4)^n0 = 8 * ||s|| * K * (3/4)^n0`
   (`regularizedZeroTail_norm_shellSum_le`, verified).

Consumer: after the global identity is formalized (next open brick), the
canonical-sum right side is bounded by `O(9^n) + brick-G + Gamma` parts on the
segment, which is `o(16^n)` against the quartic test decay — enough for the
horizontal edges to vanish.

## 4. Open bricks after G (ordered, all "new analysis" per §3b)

```text
( G-OK ) global regularized zero-sum (regularizedZeroSummable + tail bound)  CLOSED
( H ) global Hadamard/canonical-product identity for completedRiemannXi
      xi'/xi = b + sum_rho (1/(s-rho) + 1/rho)   [identity + logDeriv algebra]
( GAMMA ) |Gamma'/Gamma(s)| growth estimates on Re(s) in [0,2]  (digamma bounds;
      mathlib has no ready complex digamma bound in v4.30)
( ASM ) assemble horizontal-edge decay from principal O(9^n) + G + GAMMA
      -> rectangle limit -> Gate 2 equality (psi = spectralWeilValue)
```

RH is not claimed; Gate-3U diagnostic branch untouched.