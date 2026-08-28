# 1046 - The GATE 1 conditional assembly for the extracted table

Date: 2026-08-28.  Follows 1045.  Records the end-to-end GATE 1 assembly
leaf and the honest statement of what "finishing GATE 1" still requires.

## What landed

`ConnesWeilRH/Dev/C1CC20Gate1Assembly.lean` (+ Audit), five declarations,
all printing exactly `[propext, Classical.choice, Quot.sound]`, zero
`sorryAx`; 8-target batch build 3644 jobs clean:

1. `cc20Eq115_localGapCertificate_of_uniformGrid` - the uniform-grid
   Fact-1 table becomes the ROOT-local gap certificate of the CONCRETE
   extracted table (composes the 1045 grid layer with
   `CC20FiniteRankHalfGapCertificate.toLocalCertificate`).
2. `cc20Eq115_gapNorm_le_of_uniformGrid` - the grid mass becomes the
   equation-(121) operator-norm gap `norm(K_I - T_eq115) <= epsilon1` at
   the concrete operators.
3. `cc20Eq115_negativeForm_le_rankOne_of_uniformGrid` - CC20 Lemma
   `second`'s rank-one conclusion at the concrete operators, from the grid
   table plus the T-side coercivity block.
4. `cc20Eq115_coefficient_band_of_uniformGrid` - the concrete table's
   gamma lands the paper's band `13 < 4*gamma/log 2 < 17`.
5. `cc20Eq115_gate1Residual_nonpositive_of_uniformGrid` (flagship) - from
   grid + endpoint continuity + T-side coercivity + the trace
   identification `trace = -(4/log 2) * q(K_I)`, the slope-matched
   endpoint residual `trace - (4a/log 2) * rank <= 0` holds.  This is the
   exact algebraic shape of the certificate's `endpoint_bound` left side,
   at the repair-weight constant.

## The correction the flagship forced (a real finding)

The first draft concluded the residual at the PAPER's constant
`4*gamma/log 2`.  That conclusion is NOT derivable from this chain: the
coercivity transfer through the operator gap yields the A-weighted shift
`q + a*rank >= 0`, and the gamma-weighted form `q + gamma*rank >= 0`
would additionally need `2*ePrime >= 1`, which no landed input supplies.
The honest conclusion is therefore at the repair-weight constant
`4*a/log 2`.  The gamma-weighted residual needs a spectral certificate of
the concrete `K_I` itself - one of the named payloads below.

## The T-side spectral judgment (kills a cheap-looking route)

CC20 Lemma `first`'s input is the exceptional spectral block of `T`.  For
the extracted table `T = lambda * sum_i (P_{n_i} - d_i P_{alpha_i})` is a
sum of rank-one projections onto windowed Fourier modes.  The spectral
problem does NOT decouple into 1732 independent 2x2 blocks: the windowed
modes couple through sinc-type Gram entries
`<e_n, e_m> = integral on the log 2 window` for n != m.  A spectral
certificate therefore needs a certified eigenvalue enclosure of a
3464x3464 Gram-modulated matrix whose entries involve `log 2`
transcendentally (directed-rounding interval arithmetic over high-
precision pi and log 2 enclosures).  That is a heavy numerical-verification
project, recorded here so nobody retries the 2x2-block shortcut.

## The GATE 1 residue after this slice

The Lean machinery of GATE 1 is now wired END TO END for the concrete
table.  What remains is exactly four named payloads, none of which the
repo can honestly produce today:

| # | Payload | Type | Status |
| --- | --- | --- | --- |
| alpha | Endpoint profile enclosure `hchi` (concrete CC20EndpointSpectralData + analytic enclosure on e^abs(v) in [1, 2]) | analytic | OPEN (Sturm-Liouville regularity absent from Mathlib) |
| beta | The joint (chi - tau) uniform-grid table | data | OPEN (consumer landed in 1045; blocked by alpha) |
| gamma | T-side coercivity block (`hT`), i.e. the certified spectral enclosure of the concrete operator | data + numerics | OPEN (see judgment above) |
| delta | The archimedean comparison `trace - coefficient * rank <= W-infinity(g^2)` | analytic | OPEN (the CC20 archimedean trace-formula comparison; the W-infinity sign convention and the triple-vanishing kill of the rank-one error are landed) |

RH is not claimed.  GATE 1 is conditionally assembled: filling the four
payloads closes it, and this leaf is the single place where they meet.

## Engineering notes

- `open` is not transitive across leaf compositions: the assembly needed
  `C1CC20FiniteRankDifference` (the profile) and
  `C1CC20KernelLpLift`/`C1CC20LpOperator` (`applyKernelLp`) even though
  every imported leaf opens them internally.
- A `by` block inside a `calc` step must have its tactics indented DEEPER
  than the `by` keyword's column - continuing at the step's expression
  column fails with "expected '{' or indented tactic sequence".  Indent
  the tactic lines two columns past the step, or keep the proof on one
  line.
- `add_mul` rewrites `(a + b) * c`; `mul_add` rewrites `c * (a + b)`.
  The distributivity direction is easy to get backwards when the goal was
  normalized by `ring_nf` elsewhere - read the actual goal shape first.
- Composition-only leaves are still worth an axiom audit: the flagship's
  chain crosses four files and two structure conversions, and the audit
  is what certifies that no hidden premise crept in as an axiom.
