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
| first cell `[0, s0]` | Taylor ladder `s0 h0 + s0^2 h1/2 + s0^3 h2/3 + s0^4 h3/4` + remainder `M4Q * s0^4/96` (pole-free Q-bound; the original `s0^4 * M4/24` Leibniz form is SUPERSEDED by section 3.1) | `h0 = F0/2`, `h1 = F2 + F0/8`, `h2 = F2/2 - F0/16`, `h3 = F4 - F2/24 - 7 F0/384` (series of `N = e^{y/2}F - F0` over `sinh`, all closed forms via `F0`, `F2 = -(1/2) int (f')^2`, `F4 = (1/24) int (f'')^2` — series algebra in the y^m-coefficients: `N_1 = F0/2`, `N_2 = F0/8 + F2`, `N_3 = F0/48 + F2/2`, `N_4 = F0/384 + F2/8 + F4`, `h0 = N_1`, `h1 = N_2`, `h2 = N_3 - h0/6`, `h3 = N_4 - h1/6`); `M4Q = sup|Q''''|` on `[0, s0]` for `Q = N − T3*sinh` (`T3` = the ladder polynomial, `Q` vanishing to order 4 at 0) — the pole-free leg-sup-norm ladder of section 3.1, `sup|F^(7)|` closed by Cauchy–Schwarz with `_sup_whole(7)`; the 4th-order term is certified, not cut (`s0 = 2^-35`; the certified-width impact of every order-4+ term is `<= 1e-34`); the y^5-coefficient would need `F^(6)(0) = -int (f''')^2` and is NOT used |
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
| G-deriv  | Bump derivative chain (R_1..R_5 assembled to f')  | ABORT   |
|          | IV-eval vs centered FD of f_float (d/du           |         |
|          | convention: FD/(2h)/a, h=1e-5, RE-REGISTERED in   |         |
|          | 3.1 -- at h=1e-4 the FD truncation term exceeded  |         |
|          | the tolerance on the phase-1 carrier), at 12      |         |
|          | random interior points: CONTAINS the FD value     |         |
|          | (slack                                            |         |
|          | <= 1e-6*max(1,|fd|)); PLUS the f_float second-    |         |
|          | difference quotient shows the Richardson order-2   |         |
|          | signature at h = 2e-3, h/2, h/4 (successive        |         |
|          | differences r1, r2: |r1|/|r2| within [3.5,4.5]),   |         |
|          | i.e. the float evaluator is C^4 and the FD limit   |         |
|          | converges at the right order.  Any miss or wrong   |         |
|          | order -> ABORT.  Cross-implementation audit of the |         |
|          | chains (a shared float/IV bug would cancel the     |         |
|          | self-consistency tests here) is done by G-int vs   |         |
|          | the independent 1100b rig, not by this gate.       |         |
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

- Values: float64, vectorized (numpy), including the GL nodes/weights.
  Their rounding is covered by the REGISTERED PER-NODE backward error
  `2^-53 a half sum_i w_i (a |x_i| |dH/dx|_i + |H|_i)`, where `|H|` and
  `|dH/dx|` are the `_fvals` per-node intermediate-term magnitudes
  evaluated at the SAME float64 nodes (a valid bound: node `x_i` enters
  as `f^(j)(a x_i)`; the mean-value step for the difference leg uses the
  global sup closed forms, sigma-scaled).  The v1 worst-case form
  `2^-53 (n sup|H| + 2 sup|H'|)` — the same theorem, summed pointwise —
  was found (pre-run, on the top-K16 direction) to over-count by up to
  8 orders on high-derivative-scale carriers, because `sup|f|` x
  `sup|f''''|` ~ `1e16` while the per-node products sum to the
  integral's own scale.  The registered `2^-53` representation constant
  and every other formula are UNCHANGED.
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
  the pole-free `M4Q s0^4/96` (widow bullet below); G-mrho region
  verification retained verbatim).
- Assembly: `arb` intervals (`IV`) for the final sums, `C_ARCH`,
  `log tanh`, the ladder, and the verdict enclosures.  G-eng unchanged
  (python-flint REQUIRED).
- `eta = 0.02` exactly as section 1 states (the v1 code had drifted to
  0.028; corrected to the registered value).
- Degenerate end-of-mesh legs (the `y`-window fully inside the endpoint
  balls, core interval empty): width = closed-form pointwise endpoint-ball
  bound `a (2 - eta - sigma) B_0 B_k * 1.1` (the v1 formula) for the
  legendre family; for the entire sine family, whose `B_k` is not a bump
  bound, the derivative-sup closed form `(2a - y) sup|f| sup|f^(k)| *
  (1+1e-9)`.  The float64 VALUE is 0 (the window has shrunk to the flat
  region for legendre; for sine the whole-domain bound covers the
  leftover sliver).
- Widow remainder (`I_first`, the Taylor ladder over `[0, s0]` of section
  1): at `y ~ s0` the cancellation `N = e^{y/2} F - F0` is NOT
  float64-certifiable, so the widow evaluations run under the REGISTERED
  precision escalation (section 4: "precision escalation to 256-bit
  arb"; `flint.ctx.prec = 256`, scoped and restored), AND -- found
  necessary on the pre-run smoke of the top-K16 direction -- on
  ARB-TAYLOR-ENCLOSED nodes/weights: the float64 node representation
  term `2^-53|x_i|` times `sup|dH/dx|` (~1e14 for K-scale carriers)
  overshoots any absolute budget once it meets the leg machinery.  The
  4096-node rule is therefore built ONCE at
  an escalated RECURRENCE precision `NODE_PREC = 6700` bits by ONE arb
  pass of the 3-term Legendre recurrence plus an interval
  Taylor/mean-value certificate per node (NOT a second recurrence
  pass -- a second pass amplifies the pass-1 input interval widths
  ~1e-450 by `(1+sqrt2)^n ~ 1e1568` and overflows to +/-inf at the
  endpoint nodes: pre-run finding).  (Also pre-run: the arb
  recurrence amplifies each step's outward rounding like
  `(1+sqrt2)^m <= 3^m` -- interval dependency, NOT removed by point
  inputs: a 256-bit build ABORTS at node 0 with `|P'| absmin <= 0`;
  with `|P_m| <= 1` on `(-1,1)` the injected width per step is
  `<= 3*2^-6700`, so every pass-1 certified width is
  `<= 4096*3*2^(6493-6700) ~ 1.5e-55`.)  Per node (all interval
  quantities, arb outward-rounded):
  `p <= absmax(P_n(x_hat))`, `d >= absmin(P_n'(x_hat))`,
  `delta1 = (p + 1e-60)/d` (Kantorovich, ASSERTED `<= 1e-14`),
  `m = x_hat - P(x_hat)/P'(x_hat)`, `e = m - x_hat`,
  `[P''(x_hat)]` from the Legendre ODE `(1-x^2)P'' = 2xP' - n(n+1)P`
  at the EXACT float node with the SAME certified `P`, `P'`
  intervals, `[P'']_seg = [P''(x_hat)] +/- N3*2*delta1` (segment
  `|x - x_hat| <= 2*delta1`),
  `[P(m)] subset P + P'(x_hat)*e + [P'']_seg*e^2/2` (quadratic
  Lagrange form -- exact, no third-order truncation),
  `[P'(m)] subset P' + [P''(x_hat)]*e +/- N3*delta1^2/2`,
  `delta = absmax([P(m)]) / (absmin([P'(m)]) - max|[P'']_seg|*2*delta1)`
  with `N3 = (n-2)(n-1)n(n+1)(n+2)(n+3)/48 >= sup|P_n'''|` on
  `[-1,1]` (endpoint supremum of `P^(k)`; exact integer product,
  one float rounding, `1+1e-9` margin): by the mean-value theorem
  `x* in [m - delta, m + delta]` (asserted per node: contraction
  `delta <= delta1/2` and budget `delta <= 1e-26`, measured
  ~3e-27 -- dominated by the endpoint-node quadratic
  `P''/2*delta1^2 ~ 2.4e-20` over `|P'| ~ 8.4e6`; ABORT on failure).
  The scipy float64 root is ONLY a starting value -- its accuracy is
  never assumed.  Weights are enclosed through `z = m +/- delta` by
  `2/((1-z^2) D^2)` with `D = [P'(m)] +/- [P'']_seg*delta`.  Legs are
  arb-interval GL sums on this rule with their FULL registered widths
  (per-node residual `dmax * ~3.3e19 <= 3.3e-7` at the asserted cap,
  contribution `~ 1e-7` at the measured `dmax` -- the float64
  `2^-53|x|` form of this term was the ~3.7e3 overshoot), the ellipse
  theorem remainder at `n = 4096` -- `<= ~1e-50` sine / `<= ~1e-22`
  legendre -- and the endpoint balls.  The REMAINDER model itself is the
  pole-free Q-bound (pre-run replacement, located by the diag13
  decomposition): the section-1 form `M4 = sup|h''''|` by 4-point
  interval evaluations is NOT interval-certifiable at `y ~ s0`, because
  the Leibniz expansion `h'''' = sum C(4,j) N^(j) S^(4-j)` has
  individual `y^-5`-pole terms that cannot cancel in interval
  arithmetic (measured for top-K16 at `y = s0/8`: term `N^0 S^(4)`
  width `1.6e-12 * 3.8e58 = 6.1e46`, `|h''''| subset +/-6e46` against a
  true value ~1e3, giving `rem = s0^4 M4/24 = 3.7e3` -- seven orders
  over budget; the float-node variant failed with the SAME 3.66e3,
  proving the FORM, not the node precision, was the obstruction).  No
  width model fixes a non-cancellable form, so
  `rem = int_0^s0 (h - T3)` is bounded WITHOUT differentiating
  `1/sinh`: `T3 = h0 + h1 y + h2 y^2 + h3 y^3` is the exact Taylor-3 of
  `h = N0/sinh` at 0 (the `_h_consts` coefficient matching, table above:
  `N_m` the `y^m`-coefficients of `N0`, `h0 = N_1`, `h1 = N_2`,
  `h2 = N_3 - h0/6`, `h3 = N_4 - h1/6`), `Q := N0 - T3*sinh` vanishes
  to order 4 at 0, and Taylor's integral form with `sinh(y) >= y` gives

      rem <= M4Q * s0^4 / 96,   M4Q := sup_{[0,s0]} |Q''''|,

  which is POLE-FREE: `Q'''' = N0'''' - (T3*sinh)''''` with
  `N0''''(y) = e^{y/2} sum_i C(4,i) 2^{i-4} F^(i)(y)` and only
  `sinh`/`cosh` (bounded by `cosh(s0) <= 1.000...01`) on the polynomial
  side.  Each `sup|F^(i)|` on `[0,s0]` is the arb leg `F^(i)(s0)` above
  plus ONE mean-value step `s0 * B_(i+1)`, the ladder terminating at the
  Cauchy-Schwarz ball `sup|F^(7)| <= sqrt(F0 * 2a) * sup|f^(7)|` with
  `sup|f^(7)|` the registered closed form `_sup_whole(7)`.  Full leg
  widths are the right choice here precisely because they enter `M4Q`
  through `absmax` and a single `s0` factor.  The old `N^0 =
  (e^{y/2}-1) F + [F(y) - F(0)]` DIRECT-difference integrand
  (`_df_iv`) is REMOVED together with its consumer -- its `s`-scaled
  node rounding only ever entered the Leibniz `h''''` term the Q-bound
  replaces.  Measured pre-run: `first_cell` half-widths `~8e-24` (b0)
  and `~1.5e-8` (top-K16, `B7`-cascade dominated), inside the REGISTERED
  widow budget entry `~2e-7`; arch half-widths `1.9e-9` (b0) /
  `1.04e-7` (K16) vs the `<= 5e-7` budget, and the top-K16 arch interval
  contains the committed 1100b corrected float64 value.  Everywhere else
  on the mesh the float64 registered widths stay (the `span^5` factor
  kills every width term outside the widow); no other precision
  escalation is used.

The certified statements and the verdict mapping of sections 2 and 4 are
UNCHANGED; only the width-derivation mechanism is amended.  G-nest now
also checks interval NESTING (theta -> theta/2 single passes, no
auto-refinement).  The G-deriv row above replaces the v1 table wording
("20 points / ~16x order-4 shrinkage", which never matched any code)
with the criterion the gate actually implements (12-point containment +
order-2 Richardson signature); it is a self-consistency and smoothness
audit of the derivative chains, not a certification threshold, and
tightening it is impossible since a false chain fails containment
outright.  The FD STEP was re-registered at `h = 1e-5` (pre-run,
after the official run attempt ABORTED at `x = -0.890522` on the
phase-1 carrier, sine K=20 top): at `h = 1e-4` the truncation term
`f''' h^2/6 <= _sup_whole(3) h^2/6 ~ 2e-5` exceeds the registered
tolerance `1e-6 * max(1, |fd|)` for ANY correct chain, so the old
step made the gate unsatisfiable on the decision-relevant carrier;
at `h = 1e-5` the truncation is `~ 1e-7` and float noise `~ 1e-10`
-- the tolerance itself is UNCHANGED (a mechanism fix, not a
threshold weakening).  All other gate thresholds are verbatim.  This amendment is
committed BEFORE the first executed probe (1097b
pre-registration-before-run discipline); the pre-run smokes that located
the reversed-Horner and second-difference-denominator bugs are engine
debugging, not executed probe runs.

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