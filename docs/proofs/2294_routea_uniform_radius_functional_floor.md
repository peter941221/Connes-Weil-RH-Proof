# 2294: Uniform independent-radius functional propagation floor

Date: 2026-09-30.

Decision: SCOPED NO-GO for propagating the advertised 2293 interpolation
prices as independent, frequency-uniform complex error balls through an
absolute-value functional majorant on a window containing the origin cell.
The statement concerns this upper-bound method, not actual error, actual
Weil sign, a tail-only interval, or Filon as a whole. hgap remains open.

## Why this probe is necessary

Record 2293 priced transform interpolation errors. Its numerical comparison
with 1e7 did not price the kernel-weighted functional. This record carries
those same radii into the actual product structure before assigning a budget.
The chosen propagation discards error correlation and signed-kernel
cancellation; it therefore requires the project's cheap scoped pricing probe
before adoption. This probe rejects it on the committed class.

The finite-window functional has integrand
`K(xi) |P(xi)|^2 |B(xi)|^2 |C(xi)|^2`. Here xi is Fourier frequency,
K is the real signed physical kernel, P is the four-factor annihilator
polynomial, and B/C are the base/correction transforms. Let b/c be their
approximate magnitudes, and E/F the proposed transform error radii.

A complex error ball means that the only information retained is
`|true - approximate| <= radius`. Two independent balls allow unrelated
error phases in the base and correction channels.

## Algebraic floor of the chosen method

For the squared magnitudes, define `dB = 2b E + E^2` and `dC = 2c F + F^2`.
Then the standard nonnegative product majorant is

`H = b^2 dC + c^2 dB + dB dC`.

It equals `(b+E)^2 (c+F)^2 - b^2 c^2`, but the additive form avoids
cancellation in its numerical evaluation. All terms are nonnegative, hence
`H >= E^2 F^2`, even in the most favorable case b=c=0. Errors aligned with
their approximate complex values attain H when only independent-ball data
are retained. This does not say the actual owner errors can align independently.

Thus the absolute functional-error majorant `integral |K| |P|^2 H` has a
quartic radius floor. More accurate approximate node values cannot remove
that floor while E/F and the independent-ball interface stay unchanged.

## One complete-owner cell, without sampled quadrature

Take eta = 1e-5 and the cell `-eta <= xi <= eta`. The captured corrected
owner has support half-width 6.5536000000000025...; convolution support is
twice that radius. Directed interval exponentiation isolates the integer
cutoff 492475. A fresh integer sieve enumerates all 41136 visible prime
powers; the test compares their complete number list with the independent
existing owner enumerator. For a prime power n=p^k, its weight is
`2 log(p)/sqrt(n)`; log(p) is recomputed from the exact integer p, not lifted
from the old float weight. No old 52-term kernel is substituted.

On the cell, `cos(2 pi xi log(n)) >= 1 - (2 pi eta log(n))^2/2`.
Every right-hand side is positive, as the in-run guard checks.

The archimedean factor is
`sigma(2 pi xi) = log(pi) - Re psi(1/4 - i pi xi)`, where psi is digamma.
The reciprocal-series infrastructure is discussed in record 1734. Its
unit-anchor series has real summands

`1/(n+1) - (n+1/4)/((n+1/4)^2 + y^2)`, with y = pi xi.

These summands are nonpositive when
`y^2 <= (3/4)(n+1/4)`. The cell guard `(pi eta)^2 <= 3/16`
implies this for every n>=0. Since psi(1) is minus the nonnegative
Euler constant, `Re psi(1/4 - i y) <= 0`. Therefore sigma is positive;
zero is a conservative lower bound. This avoids a floating digamma evaluation
or a Stirling remainder in the priced kernel lower bound. The digamma test
is a transcription reference, not the analytic argument itself.

Let g be the absolute imaginary coordinate of the captured four target nodes
(g=39.25244858548658 as stored). Each polynomial factor has modulus at least
`g - 2 pi eta`; the in-run height guard checks positivity. Hence
`|P|^2 >= (g - 2 pi eta)^8` at both signs. The real offsets are not removed
from the polynomial; ignoring them here only weakens this factor-distance
lower bound.

The complete prime sum prices K at least 2801.50140289... on this cell,
and the constant weight-integral floor is

`2 eta * K_lower * (g - 2 pi eta)^8 = 3.15754323433e11`.

All these operations are interval evaluations on the full cell. No sampled
trapezoid or float extrapolation of an infinite remainder enters this floor.
The script treats the imported 2293 decimal radii as the advertised inputs
being priced, not as an independently certified outward-rounded transform
certificate. Exported interval endpoints use directed decimal FLOOR/CEILING
rounding from the exact binary endpoints.

## Results

Same captured owner and same 2293 8/16/32 ladder; budget 1e7:

```text
+----------+------------------------+-------------------+----------------------+
| subcells | majorant charge floor  | floor / budget    | common radius scale  |
+----------+------------------------+-------------------+----------------------+
| 8        | 2.70900767e35          | 2.70900767e28     | <= 7.79466476e-8     |
| 16       | 2.44776068e34          | 2.44776068e27     | <= 1.42169934e-7     |
| 32       | 7.42833974e32          | 7.42833974e25     | <= 3.40625424e-7     |
+----------+------------------------+-------------------+----------------------+
```

The floor is only for one origin cell, so the rest of the window and
arithmetic charges cannot rescue this positive-majorant method. The common
scale column is the necessary bound on s if both radii are replaced by sE/sF:
`charge_floor(s) = s^4 charge_floor(1)`. At 32 subcells the radii would need
a common reduction of at least 2.94 million times just to pass this optimistic
floor. This is necessary, not sufficient: value-dependent terms still remain.

Do not increase subdivisions of the same uniform-ball method without a named
change that can meet this scale. Admissible changes include frequency-dependent
residual information, correlated errors, or a direct functional-difference
certificate retaining signed cancellation. Tail-only intervals require their
own probe; the origin-cell ruling cannot be transferred to them.

## Verification and boundaries

Run:
`python3 scripts/routea_uniform_radius_functional_floor_2294.py`

Controls:
`python3 scripts/routea_uniform_radius_functional_floor_selftest_2294.py`

Ten tests cover exact rational product algebra, complex perturbations, aligned-
phase attainment, complete prime-power enumeration, both polynomial signs,
origin sigma reference, directed endpoint export, and all ladder artifacts.

The source and owner-capture hashes are retained in the artifact. No kernel-
weighted actual error was evaluated. No actual selected-owner readback, hgap
supplier, producer GO, or RH conclusion follows. The analytic infinite-xi tail
and the fixed-owner discrete-to-ideal bridge remain separate open obligations.

Evidence:
`scripts/routea_uniform_radius_functional_floor_2294.py`,
`scripts/routea_uniform_radius_functional_floor_selftest_2294.py`,
`results/2294_uniform_radius_functional_floor.json`.
