Record 2624: off-diagonal entry pricing selects the complex route
Date: 2026-10-07

Result

The result is positive and decisive: the hardest non-cancelling
off-diagonal entry (0,3) is priced inside its committed 2597 rectangle by
the complex residual architecture at degree 55, with a 20x box-to-width
margin. This is an external exact-rational pricing probe, not a Lean
proof: no integration backend, no Lean module, and no axiom audit is
involved. It selects route (a) complex polynomial over route (b) cos/sin
split for the upcoming Lean implementation, and it fixes the required
polynomial degree and the shared engine obligation before any table is
generated. Producer GO and RH remain false.

The pilot entry is chosen by a phase survey, not by hand. Reading the
certified producer (routea_marked_sign_arb_certificate_2337,
integrate_family), entry (row, column) is

  radius_col * Integral exp(-30/(1-x^2) + exponent*x) dx,

with exponent = (node_row + i*modulation_col) * radius_col and
radius_col = width_col^2, all operands exact captured binary64 values.
So the real coefficient of x is beta_col = node_re * radius_col and the
imaginary coefficient is psi_col = (node_im + modulation_col) *
radius_col. Both are per-column. Family zero's modulation equals
-node_im, which is the diagonal cancellation mechanism; columns 0, 1,
and 4 cancel exactly for row 0, and the remaining 27 columns are
non-cancelling. The pilot is the worst column, |psi| = 422.5447585...,
radius 5.3824..., beta 5.0863679...: pricing the hardest entry prices
all easier ones.

Why the earlier single-radius reading was wrong

The first probe draft reused the diagonal lane's owner radius
storedWidth(0)^2 for every column and omitted the per-panel rotation
exp(i*psi*center). Both errors were caught by comparison against the
committed certificate, not by taste: the probe's center sum landed at
-3.9e-38 while the certified 2597 rectangle for the pilot sits at
-3.9072971124648...e-52, and the endpoint-saddle decay estimate
exp(-sqrt(30*|psi|)) disagreed with both by orders that only the wrong
scalars explained. After the per-column correction the probe's center
reproduces the independently certified Arb enclosure to 13 significant
digits on both coordinates. The lesson is recorded: the off-diagonal
world lives on per-column radii, and the rotation factor carries the
entire cross-panel cancellation, dozens of orders of magnitude.

The degree ladder

The probe covers [-19/20, 19/20] with 190 panels of half-width 1/200,
each carrying the 2619/2621 residual architecture with the complex
numerator N_c = (beta + i*psi)*D - 60*(c+t). The exact complex
recurrence leaves the same five residual slots, the variation bound is
the real one with |beta| replaced by |beta| + |psi|, and coefficient
moduli use |q| <= |re q| + |im q| (a deliberate recorded
over-approximation by at most a factor sqrt(2)). Total box per degree:

```text
+--------+--------------------+--------------------+-----------+
| degree | partition charge   | total box          | contained |
+--------+--------------------+--------------------+-----------+
| 32     | 4.712219e-36       | 4.712219e-36       | no        |
| 42     | 1.815575e-48       | 1.815575e-48       | no        |
| 52     | 6.711942e-62       | 6.711942e-62       | no        |
| 55     | 4.273500e-66       | 4.273500e-66       | YES       |
+--------+--------------------+--------------------+-----------+
```

The committed rectangle is 8.648e-65 wide on both coordinates (the Arb
abs-tol floor), so the degree-55 box 4.273500e-66 fits with a factor-20
margin; the worst single panel is 109 at 1.277e-67. The edge region
|u| >= 19/20 is bounded by monotone phase decay: f'(u) =
-60u/(1-u^2)^2 + beta <= -60*CUT + beta < 0, so the integrand modulus
is bounded by its value at the cut, giving an edge charge of
5.04e-97 - no |psi| term enters it because |exp(i*psi*u)| = 1. The
panel [0.04, 0.05] degree-32 module cost is the calibration point: the
degree-55 tables have roughly 1.7x the coefficients and the decide+kernel
cost grows with the square, so the first off-diagonal Lean panel is
expected around 3x the diagonal panel cost.

Route selection

Both routes need cos/sin evaluation at an exact rational phase:
exp(i*psi*center) is irreducible, and omitting it loses the 47-order
cross-panel cancellation. Route (b) therefore pays the trigonometric
engine AND double real tables per panel with a product stability
theorem against trigonometric factors. Route (a) pays the engine once
and reuses the single complex recurrence, whose residual slots and
integrating-factor stability argument are already proved in the real
setting in generic form. The probe uses an external mpmath evaluation
at 160 dps, decimal round-tripped into exact Fractions, purely to price;
the Lean-side complex scalar engine is registered as a shared
obligation, not new route-(a) overhead.

Primary evidence:

  scripts/offdiagonal_residual_pricing_2624.py
  results/2624_offdiagonal_pricing.json
  scripts/routea_marked_sign_arb_certificate_2337.py (certified producer)
  results/2351_moment_matrix_witness.json (target rectangles)
  results/2275_gap_owner_audit.json (captured nodes and families)

Validation and limits

The probe's exact-rational machinery passed three negative controls
during development: the residual confinement check raises on any
nonzero low slot or sixth tail slot; the complex recurrence at psi = 0
reproduces the real diagonal coefficients; and the computed center
agrees with the committed certified rectangle to 13 digits, which is an
independent-engine cross-check, not a proof input. Everything here is
pricing: pricing_lean_verified=false and
actual_entry_containment_lean_verified=false in the payload. The
containment verdict means the architecture, degree, and engine suffice;
making it a theorem is exactly the next brick.

Reproduction interface

Run scripts/offdiagonal_residual_pricing_2624.py with a Python that has
mpmath; it re-reads the committed capture and witness, re-runs the
survey, and rewrites the payload. No Lean, no workspace, no WSL state
is involved.

Next steps

1. Extend the 2620 scalar engine to complex arguments: cos/sin at exact
   rational phase with 320-bit coordinates and 400-bit radii, replayed
   in Lean through decide+kernel exactly like the real engine.

2. Add the complex list helpers and the complex residual stability
   theorem at degree 55, then generate the pilot entry's 190 complex
   panel tables with the 2622 batch machinery as the template.

3. Assemble the 190-panel partition plus the monotone edge bound into
   the actual (0,3) entry containment theorem, keeping the committed
   2597 rectangle as the target. Only then widen row 0 to all 27
   non-cancelling columns.
