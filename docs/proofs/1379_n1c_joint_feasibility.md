# 1379 — N1c: joint feasibility, the norm budget, and the falsifier resolution

Date: 2026-09-13. Consumes [1377](1377_n1a_global_mass_bridge.md) (Lemma
A / A-prime, kernel constant), [1378](1378_n1b_band_bridge.md) (Lemmas
C / D, coupling constants), [1376](1376_n0p_closure_and_n1_recon.md)
§2c (the falsifier), [1371] (invisible-anchor floor `||g||^2 >=
4/B_R(d)`), and the register orbit definitions cited in §2.
Evidence class: PAPER ONLY. The small-d verdicts in §4 are MODEL-lane
arithmetic on the [1371] asymptotic and the [1378] couplings (law 65)
and carry no closure claim. RH NOT claimed.

## 1. The question N1c must answer

[1376] section 2c left the vertical bridge with one falsifier: "if the
coupling term always dominates, the bridge is real only in cells where
the constructed norm is controlled". This record resolves the
falsifier into an exact feasibility statement and identifies the
missing producer. The S5 consumption chain is:

```text
value constraint   : |G(s_v)| = 1 at the vertical point s_v (the
                     Laplace-coordinate image of the off-line zero),
band bridge [1378] : B_delta >= (delta/2)*|G(s_v)|^2 - C_min * ||g||^2,
                     C_min := min(C_C, C_D)  (global-window worst case),
norm floor [1371]  : ||g||^2 >= F := 4 / B_R(d)   (killed prefix),
Plancherel cap     : B_delta <= 2*pi*||g||^2.
```

The construction is free to choose `||g||^2 >= F` subject to the value
constraints; the delivery is maximized by the SMALLEST admissible norm.
So the delivered band mass satisfies

```text
B_delta >= (delta/2) - C_min * max( 1/x*, F ),
x* := sup { |G(s_v)|^2 / ||g||^2 :  g subject to the constraint set }
```

and the bridge is executable in a cell iff BOTH

```text
(J1)  x* > 2 * C_min / delta,          (ratio condition, [1378] map)
(J2)  delta * B_R(d) > 8 * C_min.      (norm-budget condition, NEW)
```

(J2) is the [1376] falsifier made into a theorem: the coupling can be
beaten only if the construction's norm is BUDGETED ABOVE by
`||g||^2 <= delta/(2*C_min)`, while [1371] budgets it BELOW by `F`.
The two budgets squeeze: `4/B_R(d) <= ||g||^2 <= delta/(2*C_min)`.

## 2. Lemma E (the constrained ratio x* is an explicit finite form)

Work in `H := {G(s) = Integral[a..b] g(x) e^(sx) dx : g in L^2(a,b)}`
with `||G|| := ||g||_2` (the [1377] setup). Constraint nodes `w_1..w_N`
(distinct complex numbers) with prescribed values `y_j`. Let

```text
Gamma_ij := K(w_i, w_j),   K(s,u) := Integral[a..b] e^((s + conj(u)) x) dx
          = (e^((s+conj(u))b) - e^((s+conj(u))a)) / (s + conj(u)).
```

`K` is the reproducing kernel of `H` (`G(u) = <G, K_u>`; the diagonal
`K(s,s) = Integral e^(2 Re s x) dx` is exactly the [1377] Lemma A
constant). `Gamma` is positive definite for distinct nodes (the
`K_u = e^(conj(u)x)` are linearly independent in `L^2`).

```text
Lemma E.  The unique minimal-norm G in H with G(w_j) = y_j has
          ||G||^2 = y* Gamma^(-1) y.
          In particular, for a single value-1 constraint at s_v with
          the remaining nodes killed (y = e_1 after ordering),
          x* = 1 / (Gamma^(-1))_11
             = K(s_v,s_v) - k* Gamma_Z^(-1) k      (Schur form),
          k := (K(w_j, s_v))_{j >= 2}.
```

Proof: interpolants are `G = Sum c_j K_(w_j)`; the constraints read
`Gamma c = y`, and `||G||^2 = c* Gamma c = y* Gamma^(-1) y`. The block
inverse of `[[K(s_v,s_v), k*], [k, Gamma_Z]]` gives the Schur form;
`(I - P_Z)K_(s_v)` attains it. QED.

Consistency checks. (i) No constraints: `x* = K(s_v,s_v) = K_A` —
exactly [1377] Lemma A-prime. (ii) A kill node approaching `s_v`:
`x* -> 0` continuously — kills at the vertical point are catastrophic,
kills far away cost little, quantified by the kernel entries. (iii)
Register instance (verified in source): the orbit is the FOUR-POINT
functional-equation set `{rho, 1 - conj(rho), conj(rho), 1 - rho}` with
value pattern `rho -> 1, 1 - conj(rho) -> -1, others -> 0`
(ConnesWeilRH/Source/CC20YoshidaFullProduct.lean:52-61), joined by the
healthy targets `healthyUnscaledTargetNodes = orbit + {rho + 1/2, 1/2,
1, 3/2}` — a FINITE node list; `y* Gamma^(-1) y` is finite linear
algebra over elementary functions. NOT an integer-translate lattice,
so no Toeplitz reduction applies; the 4x4(+targets) Gram is directly
computable instead.

Consequence for the ledger: the B5 interpolation feasibility constant
is `K_loc := y* Gamma^(-1) y` — this is what N2's program must bound,
now with an explicit formula. (The earlier K_loc placeholders —
[1372] S5's local comparison constant — reduce to this object plus the
[1378] coupling constants.)

## 3. The joint feasibility theorem

```text
Theorem (N1c).  Fix the window (a,b), the vertical point s_v with
Re s_v = d > 0, constraint nodes with value pattern y, and delta > 0.
A detector in H satisfying the constraints delivers a vertical band
bridge (B_delta > 0 with the [1378] lower bound effective) only if

  (J1)  y* Gamma^(-1) y < delta / (2 C_min),   and
  (J2)  F < delta / (2 C_min),  i.e.  delta * B_R(d) > 8 * C_min

        whenever the [1371] floor binds (killed-prefix class).

If the construction is NOT subject to the [1371] floor (norm budget
controlled from above), (J2) drops and (J1) alone decides.
```

Proof: assembly of §1; the delivery bound is (δ/2)·|G(s_v)|² −
C_min‖g‖² with |G(s_v)|² = 1 forced and ‖g‖² ≥ max(1/x*, F) the
smallest admissible norm; positivity requires the two displayed
inequalities. QED.

## 4. Consequences: the falsifier fires in the killed-prefix class

MODEL-lane arithmetic (labels binding): with the [1371] small-d form
`F ~ 3/(2 d^2 R^3)` and the [1378] small-d couplings `C_C ~ 8 pi d^2
R^2`, condition (J2) reads

```text
delta * (8/3) d^2 R^3 > 64 pi d^2 R^2   <=>   delta > 24 pi / R,
```

and the delta^3 term of `C_C` re-enters at that scale: balancing
`delta/3 > 8 pi/R + 2 delta^3/d^2` has NO positive solution for small d
(the d-free term `8 pi/R` cannot be overcome — the left side dies like
`d^2`). Route D fails even earlier (its d^2-coupling against the
d^(-2)-floor cancels to an impossible `d^2R^2 > 6(e^(dR)-1)^2 + ...`).

```text
VERDICT (killed-prefix class): in cells where the [1371] floor binds,
the GLOBAL band bridge delivers nothing at small d — the [1376]
falsifier FIRES. This is not a new obstruction: it is the
invisible-anchor fact seen from the bridge side. A construction whose
mass is forced into the invisible complement cannot simultaneously
deliver visible band mass near t0.
```

```text
VERDICT (budget-controlled class): if the constructed family escapes
the invisible-anchor pathology — the counterterm places the anchor
VISIBLY, so no floor below delta/(2 C_min) is forced — then (J1)
alone decides, and by the [1378] regime map the bridge is executable
in the near-line band `dR <~ 0.53` (route D) with `x*` close to its
unconstrained ceiling `K_A` whenever the constraint nodes stay clear
of s_v (Lemma E, consequence (ii)).
```

Campaign directive (the designed-together clause resolved): the
vertical bridge is not blocked by analysis. It is blocked by the
CONSTRUCTION CLASS. Exactly one of:

```text
(A)  design a visible-anchor family with an explicit NORM BUDGET
     ||g||^2 <= delta/(2 C_min)  — a new producer target (N2-beta);
(B)  restrict the closure to the near-line band, where the budget
     condition is replaced by the ratio condition alone.
```

## 5. Board changes

| row | state |
|---|---|
| N1c | DONE at paper level (this record): feasibility theorem + falsifier resolution |
| N2 | retargeted: `K_loc := y* Gamma^(-1) y` (Lemma E, explicit finite form) |
| N2-beta (NEW) | visible-anchor norm budget `||g||^2 <= delta/(2 C_min)` (branch A) |
| N3 | unchanged; density allowance `lambda_delta` enters (J1) additively: `x* > 2(C_min + lambda_delta)/delta` |
| N1d | upgrade: Lemma E is a small formal candidate (finite Gram, elementary kernel; needs the L^2 interface export as before) |

## 6. Honesty ledger

- PAPER ONLY; no Lean statement, no digits. The §4 verdicts are
  MODEL-lane arithmetic on the [1371] asymptotic and [1378]
  worst-case couplings (law 65); any rig confirmation follows the
  1373 amendment protocol (prereg BEFORE digits).
- `C_min` is the GLOBAL-window worst case; construction-side moment
  control ([1378] §5) can only SHRINK it, which helps both (J1) and
  (J2) — the verdicts are conservative.
- Branch (A) vs (B) is an owner-facing route decision, not decided
  here.
- RH NOT claimed; stop word unchanged (gate Lean certificate, 1358).
