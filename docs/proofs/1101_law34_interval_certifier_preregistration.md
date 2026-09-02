# 1101 - law-34 certified interval arch certifier (pre-registration)

Date: 2026-09-02.

Status: PRE-REGISTRATION, committed BEFORE the run.  This record builds the
first brick of the certified-upper-bound machinery named by record 1100b
section 5.3 (law 34): a rigorous interval-arithmetic evaluator for the
`orbitWindowSemiLocalGate` functional on explicit carrier functions, with
all quadrature remainders bounded by theorem-valid formulas, replacing the
float64 passes of the 1100/1100b rigs.  Consumer (map `004` section 2,
record 1099): the single gate Prop `orbitWindowSemiLocalGate g` on the
pinned orbit detector; the all-of-`V` form `Q <= 0` on the triple-vanishing
subspace is the zero-design shape.  RH is not claimed; GATE 1 untouched;
evidence level NUMERICAL with certified-interval bounds (a certificate
INPUT for a later Lean brick, following the `scripts/yoshida_intervals/`
exact-certificate precedent).  The probe is
`1101_law34_interval_certifier_probe.py`.

## 1. What is certified, and the machine shape

Gate bookkeeping (map `004` section 3): `qw(g) = -arch(F_g) - finitePrimeSum(F_g)`
with `F_g = g.convolutionSquare`; the gate needs `Q := arch + prime <= 0`.
Both functionals are evaluated here for EXPLICIT `f = coeffs @ basis`
(basis = legendre x smooth_bump or sine on `[-a, a]`, exactly the 1100b
carrier):

```text
arch(f)  = C_ARCH * F(0) + I_body + F(0) * log(tanh a),
I_body   = int_0^{2a} h(y) dy,
h(y)     = (e^{y/2} F(y) - F(0)) / sinh(y),   h(0) = F(0)/2 (removable),
F(y)     = int_{-a}^{a-y} f(u) f(u+y) du,
prime(f) = 2 * sum_q (Lambda(q)/sqrt(q)) * F(log q)   (visible prime powers),
```

`C_ARCH = log(4*pi) + gamma` (the 1020 rig convention).  The
first-cell sliver of records 1100/1100b is ABSENT here: the body starts at
`y = 0` with the removable limit, so no polarization-shift identity exists —
this is the true continuum arch of the same object the corrected float64
rig approximates.

Certified-evaluation design (every number an interval; every quadrature
remainder a theorem-valid formula; no float64 node or weight trusted):

| Piece | Rule | Remainder control |
|---|---|---|
| `F(y)`, `F(0)`, `F(log q)`, moment squares | Gauss-Legendre on the interior core `[-1+eta, 1-eta-y/a]` + two endpoint ball cells of width `eta = 0.02` (legendre family only; the sine family is entire and needs no balls) | core remainder `|E| <= 8 * M_rho * rho^{1-2n} / (rho^2-1)` (REGISTERED constant 8 vs the classical Chebyshev-coefficient bound `2 M rho^{-k}` summed over k >= n, x2 margin) with `rho = 1 + 0.9 * eta/half`; `M_rho` a CLOSED-FORM theorem bound (triangle inequality + `|1-z^2| >= Delta` with `Delta = 0.9*(2 eta - eta^2)`, `|exp(-1/(1-z^2))| <= exp(1/Delta)` on the region, `|poly(z)| <= P * Rx^deg`, `|R_m(z)| <= N_m * Rx^deg / Delta^{2m}`; both `Delta` and the bounds VERIFIED by G-mrho on the ellipse boundary) — no sampling, no margin; GL node/weight float64 rounding REGISTERED `n * 2^-52 * (n * sup|H| + 2 * sup|H'|)`; ball cells `|int| <= eta * a * B_0 B_k` with closed-form pointwise `B_k = bsup * (1/a)^k * sum_j C(k,j) P_j N_{k-j} (1.98 eta)^{-2(k-j)}`, `bsup = exp(-1/(2 eta - eta^2))`, sup-at-inner-edge REGISTERED (`eta = 0.02 < 1/(4*8)`, each `(b R_m)` term increasing on the cell); n_gl = 4096 |
| `I_body` | composite Simpson on the adaptive mesh `y_{j+1} = y_j (1+theta)` from `s0`, 3 h-evals per cell | `|E_j| <= span^5 * M4_cell / 90` per cell, `M4_cell <= max |h''''|` over the cell by absolute-max unary interval evaluation at 3 nodes (h'''' is interval-evaluable everywhere on the mesh: cells avoid 0), x1.16 theta REGISTERED safety |
| first cell `[0, s0]` | Taylor ladder `s0 h0 + s0^2 h1/2 + s0^3 h2/3 + s0^4 h3/4` + remainder `s0^4 * M4/24` | `h0 = F0/2`, `h1 = F2 + F0/8`, `h2 = F2/2 - F0/16`, `h3 = F4 - F2/24 - 7 F0/384` (series of `N = e^{y/2}F - F0` over `sinh`, all closed forms via `F0`, `F2 = -(1/2) int (f')^2`, `F4 = (1/24) int (f'')^2` — series algebra in the y^m-coefficients: `N_1 = F0/2`, `N_2 = F0/8 + F2`, `N_3 = F0/48 + F2/2`, `N_4 = F0/384 + F2/8 + F4`, `h0 = N_1`, `h1 = N_2`, `h2 = N_3 - h0/6`, `h3 = N_4 - h1/6`); `M4 = sup|h''''|` on `[0, s0]` by interval evals at 4 positive points x a REGISTERED `(1 + 4 s0)` growth margin — the 4th-order term is certified, not cut (`s0 = 2^-35`; the certified-width impact of every order-4+ term is `<= 1e-34`); the y^5-coefficient would need `F^(6)(0) = -int (f''')^2` and is NOT used |
| tail `F0 log tanh a`, `C_ARCH`, | arb certified primitives | directed-rounding interval arithmetic (python-flint `arb`, 80 bit default, 256-bit escalation pre-approved) |
| `h'` | closed form with `F`, `F'` | `F'(y) = int f(u) f'(u+y) du` (boundary terms vanish: `f(+-a) = 0`) |
| derivative chains | bump `R_m` via recurrence `R_{m+1} = R'_m + R_m * rho'`, `rho = -1/(1-x^2)`, generated programmatically to order 5; Legendre-derivative polynomials exact | audited by G-deriv (finite-difference containment + order-signature), never by belief |

Ladder-cut honesty: `s0 = 2^-35` makes every order-4+ contribution to the
certified enclosure `<= 1e-34`; the cut is named and bounded, not ignored.

## 2. What the certified numbers would mean

The certified statements are bounds for ONE explicit function at a time (a
law-34 compliant step: the certified inclusion of the finite Galerkin space
in the continuum carrier and the spectral-gap reduction to `sup_V` are
SEPARATE, later bricks).  The ALL-of-`V` statement is not attempted here.

- If a certified `Q_top < 0` with margin above the certified width: the
  gate is alive on that explicit `V`-direction with the project's first
  RIGOROUS arch/prime bounds; the envelope is then the certified
  spectral-gap reduction (name the next brick).
- If a certified `Q_top > 0` with margin above the certified width: that
  EXPLICIT triple-vanishing function carries positive gate price; the
  all-of-`V` sign statement is false as a statement about this carrier
  family at that radius; a C3 sign proof would then have to restrict to
  the detector subclass (the pinned object itself, which can be certified
  directly by this same machine — that is the path, not a scan).  NOT
  evidence against RH either way.
- If the interval straddles zero: no separation at the certified width
  budget; report the width table — the machine itself is still the
  deliverable (law-34 brick 1), and the straddle transfers the target to
  the spectral-gap reduction verbatim.

## 3. Gates (pre-registered; abort discipline as in 1097/1100/1100b)

```text
+----------+----------------------------------------------------+---------+
| Gate     | Criterion                                          | Class   |
+----------+----------------------------------------------------+---------+
| G-eng    | python-flint `arb` loads, version printed;         | ABORT   |
|          | REQUIRED (no mpmath.iv fallback: certification     |         |
|          | claims are the product).                            |         |
| G-deriv  | Derivative chains (bump R_1..R_5, h', F') vs      | ABORT   |
|          | centered finite differences at 20 rational points: |         |
|          | intervals CONTAIN the FD values AND shrink by      |         |
|          | ~16x per halving (order-4 signature); any miss or  |         |
|          | wrong order -> ABORT.                              |         |
| G-mrho   | The REGISTERED region bounds hold on the ellipse   | ABORT   |
|          | boundary: `|1-z^2| >= Delta = 0.9*(2 eta - eta^2)` |         |
|          | and `|Re(1/(1-z^2))| <= 1/Delta` at 64 sampled     |         |
|          | boundary points of the core x-ellipse (arb, 3x     |         |
|          | margin), plus `M_rho(0.9 rho)/M_rho(rho)` INSIDE   |         |
|          | the closed-form envelope (theorem, not sampling)   |         |
|          | reported.  Any violation -> ABORT.                 |         |
| G-nest   | Halving the y-cells halves the certified width     | ABORT   |
|          | (>= 1.9x ratio) AND new interval NESTED inside    |         |
|          | old, on one (family, radius) case.                 |         |
| G-int    | Certified arch interval [L,U] CONTAINS the         | ABORT   |
|          | committed 1100b corrected float64 value (bias      |         |
|          | allowance 1e-5 abs over the grid-32001 trapezoid)  |         |
|          | on the six G-cell-3 functions; width U-L reported. |         |
| G-prime  | Certified prime leg [L,U] CONTAINS the float64     | ABORT   |
|          | recomputation on the three arch-top directions;    |         |
|          | width reported.                                    |         |
| G-rows   | Per function: moment residual <= 1e-10 /           | DISCARD |
|          | orthonormality <= 1e-10 (same as 1100/1100b),      |         |
|          | total-top eigenvector recomputed and logged.       |         |
+----------+----------------------------------------------------+---------+
```

Certified-width budget per run: arch leg and prime leg each targeted to
`<= 5e-7` half-width (total `Q` width `<= 1e-6`), by adaptive y-cell
refinement (theta solved from the certified-width target with the
leading term `24 theta^5 / 90` per cell) up to 2e5 cells and the
Gauss-Legendre core (n_gl = 4096) with the REGISTERED remainder stack of
the table above; budget exhaustion reports "straddle at budget" (no
verdict, recorded).

## 3.1 Pre-run amendment (v2 arithmetic model; committed before any run)

The v1 design evaluates every GL node in `arb` interval arithmetic.  The
smoke validation showed (a) the per-node interval loops are ~1000x too
slow on the shared machine, and (b) the interval widths at the widow
nodes are in fact DOMINATED by engine rounding, not by the theorems:
the `h''''` interval at `y = s0` is ~1e28-wide (2^-80 times the ~1e44
cancelling Leibniz terms), the same enclosure class a float64 evaluation
gets with a registered forward-error bound.  The v2 model is therefore
the honest and faster route to the SAME certified enclosures:

- Values: float64, vectorized (numpy), including the GL nodes/weights
  (their rounding stays covered by the REGISTERED perturbation term
  `2^-53 (n sup|H| + 2 sup|H'|)`, unchanged).
- Arithmetic widths: REGISTERED forward error analysis.  Each f^(k)
  node value carries a magnitude sum `M >= sum |intermediate terms|`
  tracked in the same pass; the leg arithmetic error is bounded by
  `2^-52 * C * M` with the REGISTERED op-count constants
  (`C_FVAL = 4096` per-node evaluation chain including the exact-integer
  `R_m` and dyadic Legendre `polyval` chains, `C_DOT = 512`, assembly
  margins).  The `h`-machinery (`N^(j) = e^{y/2} sum C(j,i) 2^-i F^(j-i)`,
  `S^(m) = u P_m(coth y)`, Leibniz to order 4) is evaluated in `wadd/
  wmul` pair arithmetic: `(value, width)` with per-op `2^-52 * 4 *
  magnitude` margins.  These constants dominate nothing: every term is
  <= ~1e-10 where the mesh remainder is ~1e-7.
- Theorem remainders: UNCHANGED from section 1 (ellipse `8 M_rho
  rho^{1-2n}/(rho^2-1)` with the closed-form `M_rho`; endpoint balls
  `eta a B_0 B_k`; mesh Simpson `span^5 M4_cell/90`; Taylor ladder with
  `s0^4 M4/24`; G-mrho region verification retained verbatim).
- Assembly: `arb` intervals (`IV`) for the final sums, `C_ARCH`,
  `log tanh`, the ladder, and the verdict enclosures.  G-eng unchanged
  (python-flint REQUIRED).
- `eta = 0.02` exactly as section 1 states (the v1 code had drifted to
  0.028; corrected to the registered value).

The certified statements, gates, thresholds, and verdict mapping of
sections 2-4 are UNCHANGED; only the width-derivation mechanism is
amended.  G-nest now also checks interval NESTING (theta -> theta/2
single passes, no auto-refinement).  This amendment is committed BEFORE
the first executed probe (1097b pre-registration-before-run discipline).

## 4. Verdict mapping (pre-registered)

```text
any ABORT-class gate fails -> ABORT: no verdict, no repo change.
(fixes restricted to pre-registered amendments: precision escalation to
 256-bit arb; sampler density 4001; y-cell budget 4e5; u-grid 2^17 —
 each amendment recorded, not re-registered; 1100 G-arch precedent.)

Directions certified: the three 1100b arch-top directions (a=2 leg K=16,
a=4 leg K=24, a=2 sine K=20) and the three TOTAL-gate top directions
(arch+prime eigenvector, same (a, family, K)), plus the three plain
G-cell-3 basis rows.

H1c CERTIFIED-POSITIVE-GATE (numerical, certified bounds):
   some certified L_total > 0 (margin >= certified width)
   -> explicit triple-vanishing witness with positive gate price at its
      radius: all-of-V sign false there; C3 sign restricted to the
      detector subclass; map 004 P2 row updated (NUMERICAL); the pinned
      object certified directly is the named next probe.
H2c CERTIFIED-NEGATIVE-GATE (numerical, certified bounds):
   every certified U_total < 0 (margin >= certified width)
   -> gate alive with rigorous arch/prime bounds; the named next brick
      is the certified spectral-gap reduction from V to the finite
      subspace (law 34 part 2).
else STRADDLE: no separation at the certified width budget; widths
   recorded; spectral-gap reduction is the next brick either way.
```

No repo change is keyed to any branch except this record's verdict
section and, for H1c/H2c, the map 004 P2 status row labeled NUMERICAL.
README untouched (README change guard).

## 5. Verdict (appended after the run)

(Pending.)