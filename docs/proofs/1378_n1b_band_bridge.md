# 1378 — N1b: the local band bridge (paper beat)

Date: 2026-09-13. Consumes [1377](1377_n1a_global_mass_bridge.md)
(Lemma A / A-prime, general-window constants), [1376]
(1376_n0p_closure_and_n1_recon.md) §2 (mass-form deliverable, pointwise
dead), [1371] Plancherel convention (:210-229).
Evidence class: PAPER ONLY. All constants explicit; the regime numbers in
§4 are MODEL-lane arithmetic on MODEL placeholder constants (law 65) and
carry no closure claim. RH NOT claimed.

## 1. What S5 consumes and what must be proved

The gain leg of 1372 S5 compares LINE MASS near `t0` against the local
zero density. Since [1376] section 2a killed the pointwise form, the
deliverable is a lower bound for the band mass

```text
B_delta := Integral[t0 - delta .. t0 + delta] |G(i*t)|^2 dt
```

in terms of the off-line value `|G(d + i*t0)|^2`, with the price expressed
through `||g||^2` (the coupling that [1376] section 2c and [1377] section
5 fix as the N1c interface). In the [1376] shape `B >= |G|^2/B(d,delta,W)
- K_loc * coupling * ||g||^2` the lemmas below take `1/B(d,delta,W) =
delta/2` and identify the coupling bracket explicitly.

Conventions as in [1377]: `G(z) = Integral exp(z*x) g(x) dx` (positive
character, register `laplaceAt`, CC20YoshidaConvolution.lean:35-56), `g`
smooth, compactly supported in the window `(a, b)`, center `m =
(a+b)/2`, width `W = b - a`, `d > 0`, and (P0)
`Integral |G(i t)|^2 dt = 2*pi*||g||^2`.

Two monotone building blocks are used repeatedly:

```text
(u - v)^2 >= u^2/2 - v^2          (split inequality),
|u + v|^2 <= 2|u|^2 + 2|v|^2      (parallelogram bound).
```

## 2. Lemma D (damping-split route)

The off-line value is the transform of the damped profile; damping is a
max-norm perturbation of the identity on the window:

```text
g_d := g * e^(d x) = e^(d m) * g + h,   h := g * (e^(d x) - e^(d m)),
||h||_2 <= (e^(d b) - e^(d a)) * ||g||_2,                (D1)
G(d + i*t0) = e^(d m) * G(i*t0) + F[h](t0),
|F[h](t0)| <= sqrt(W) * (e^(d b) - e^(d a)) * ||g||_2.   (D2)
```

(D1) uses `max_{[a,b]} |e^(dx) - e^(dm)| = e^(dm)(e^(dW/2) - 1) =
e^(db) - e^(da)`; (D2) is Cauchy–Schwarz against the unit-modulus
character. Rearranged:

```text
|G(i*t0)| >= e^(-d m)|G(d + i*t0)| - eps_0 * ||g||_2,
eps_0 := e^(-d m) * (e^(d b) - e^(d a)) * sqrt(W).       (D3)
```

Continuity floor: `|G(i*t0) - G(i*t)| <= c * |t0 - t| * ||g||_2` with

```text
c := sqrt( Integral[a..b] x^2 dx ) = sqrt( W*m^2 + W^3/12 ),
```

so on the band `|G(i t)|^2 >= |G(i t0)|^2/2 - c^2 delta^2 ||g||^2`
(split inequality), and integrating over the band,

```text
B_delta >= delta * |G(i*t0)|^2 - 2 * c^2 * delta^3 * ||g||^2.  (D4)
```

Chaining (D3) into (D4) with the split inequality:

```text
Lemma D.  B_delta >= (delta/2) * e^(-2dm) * |G(d + i*t0)|^2
                    - [ delta * eps_0^2 + 2 c^2 delta^3 ] * ||g||^2.
```

Symmetric window `(-R, R)`: the split can be taken directly at 1
(`h = g(e^(dx) - 1)`, max norm `e^(dR) - 1`), removing the `e^(-dm)`
penalty (`m = 0`) and sharpening the constant:

```text
B_delta >= (delta/2) * |G(d + i*t0)|^2
           - [ 2 R delta (e^(dR) - 1)^2 + (4/3) delta^3 R^3 ] * ||g||^2.
```

## 3. Lemma C (band-average kernel route)

The second route avoids the point value `G(i*t0)` entirely and is clean
under window shift. Let

```text
avg := (1/(2 delta)) * Integral[band] G(d + i*t) dt,
M_d := sup_t |d/dt G(d + i*t)| <= Integral[a..b] |x| e^(dx) |g(x)| dx
       <= ( max_{[a,b]} |x| e^(dx) ) * sqrt(W) * ||g||_2,
```

(the exact Cauchy–Schwarz weight `Integral x^2 e^(2dx)` may replace the
max form). Then `G(d + i*t0) = avg + error` with `|error| <= delta*M_d`
(mean value), and

```text
|avg|^2 <= (1/(2 delta)) * Integral[band] |G(d + i*t)|^2 dt
        <= (1/(2 delta)) * ( 2 B_delta + 4 pi ||h||^2 ),
```

using `G(d + it) = G(it) + F[h](t)`, the parallelogram bound, and
Plancherel for `h` off the band. Assembling:

```text
|G(d + i*t0)|^2 <= (2/delta) B_delta + (4 pi / delta)||h||^2 + 2 delta^2 M_d^2,
```

that is:

```text
Lemma C.  B_delta >= (delta/2) * |G(d + i*t0)|^2
                    - [ 2 pi (e^(d b) - e^(d a))^2
                        + delta^3 * W * (max_{[a,b]} |x| e^(dx))^2 ] * ||g||^2.
```

Symmetric window, small `d`: coupling `≈ 8 pi d^2 R^2 + 2 delta^3 R^3`.
Note the signal coefficient carries NO `e^(-dm)` factor: the window
center is paid once inside `e^(db) - e^(da)`, not on the signal side.
This is the flat-box (Dirichlet) kernel form of the planned
`W_{t0,delta}` projection; a Fejér-type positive kernel changes the
`delta^3` constant but cannot remove the damping term `2 pi
(e^(db)-e^(da))^2` — that term is the [1377] Lemma A-prime operator-norm
obstruction reappearing, as it must.

## 4. The two routes compared; delta-optimization

Write `X := |G(d + i*t0)|^2 / ||g||^2` and recall the attainable ceiling
[1377] Lemma A-prime: `X <= K_A := (e^(2db) - e^(2da))/(2d)`. Both
lemmas read `B_delta/||g||^2 >= (delta/2) X - coupling(delta)`; the
bridge is informative when the right side is positive at the ceiling.

| route | coupling (symmetric, small d) | informative regime (extremal X) |
|---|---|---|
| D (damping-split) | `2 d^2 R^3 * delta + (4/3) delta^3 R^3` | `dR < ln(1+2^(-1/2)) ≈ 0.53` and `delta <~ 0.61/R` |
| C (band-average) | `8 pi d^2 R^2 + 2 delta^3 R^3` | `dR <~ 0.10` (delta-free leading term) |

Derivations: route D is informative iff `X > 4R(e^(dR)-1)^2 +
(8/3)delta^2 R^3`; at `X = K_A ≈ 2R` the exact width condition is
`(e^(dR)-1)^2 < 1/2`, i.e. `dR < ln(1 + 2^(-1/2)) = 0.5348...` (the
linearized form `d^2R^2 < 1/2` giving `0.71` overestimates by ~34% and
is valid only as `dR -> 0`), and `delta^2 < 3/(8R^2)`. Route C at
extremal `X`: maximize `S(delta) = (delta/2)X - c1 - c2 delta^3` with
`c1 = 8 pi sinh^2(dR)`, `c2 = 2R^3 e^(2dR)`; `delta* = sqrt(X/(6 c2))`,
and the maximum is positive iff `X^(3/2) > 3 sqrt(6 c2) c1`, which at
small `d` reads `2^(3/2) R^(3/2) > 48 sqrt(3) pi d^2 R^(7/2)`, i.e.
`dR < 0.10` (linearized; the exact constant is defined implicitly by
`X(c1,c2)` above).

MODEL-lane reading (placeholder constants; no closure claim): with `R =
n + 2` the damping-split route carries extremal signal up to

| n | R | d_max ≈ 0.53/R |
|---|---|---|
| 1 | 3 | ~ 0.18 |
| 4 | 6 | ~ 0.09 |
| 8 | 10 | ~ 0.05 |

where `d = Re rho - 1/2`. Honest reading: the PURE global band bridge
covers the near-line band at each window scale; larger `d` requires
construction-side input (the subfamily evaluation norm, [1377] A-prime
door (ii)) or the density-side race of N1c. The best bound at any point
is `max(Lemma C, Lemma D)`; they are complementary, not redundant — C is
shift-clean with a narrow regime, D has the wide regime but carries the
`e^(-2dm)` signal factor in general windows.

At `d -> 0` both routes degenerate to the sigma-line statement
(`B_delta >= delta|G(it0)|^2 - O(delta^3 R^3)||g||^2`, the continuity
floor alone): chain-end consistency with [1377] Corollary B.

## 5. Where N2 and N1c plug in

1. N2 (`K_loc`): both coupling brackets contain window-moment terms
   (`Integral x^2`, `Integral x^2 e^(2dx)`, and route D's split norms).
   First-moment/derivative control of the CONSTRUCTED family — the N2
   program — tightens exactly these terms; the spline family's moment
   structure is the natural input. Open.
2. N1c: Lemma D/C bounds `B_delta` from below ONLY through `||g||^2`
   the coupling. [1371] forces `||g||^2 >= 4/B_R(d)` on the killed
   prefix, so the joint inequality must compare `(delta/2)|G(d+it0)|^2`
   against `coupling * 4/B_R(d)` plus the density race
   (`B_delta >= eta(t0) * 2 delta` side). That comparison is the next
   record, not this one.
3. Falsifier (unchanged from [1376] section 2c): if the coupling always
   dominates, the bridge holds only where the constructed norm is
   controlled, and that condition becomes an explicit hypothesis of the
   closure theorem.

## 6. Honesty ledger

- PAPER ONLY: no Lean statement; N1d remains blocked on the `L^2`
  interface export ([1377] section 6).
- No digits: the regime numbers in §4 are MODEL-lane arithmetic on
  placeholder constants (law 65); nothing requires a preregistered run
  (law 42 untouched); any rig sweep of the `dR`/`delta` regime map must
  follow the 1373 amendment protocol (prereg BEFORE digits) — this is
  N1e, not fired here.
- Lemma C's Fejér-refinement clause and Lemma D's exact-C-S weighted
  form (`Integral x^2 e^(2dx)`) are stated as remarks, not developed.
- RH NOT claimed; stop word unchanged (gate Lean certificate, 1358).
