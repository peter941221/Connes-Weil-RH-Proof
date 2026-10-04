Record 2574: same-owner chord bound for the correction-second integral

Verdict: GENERIC LEAN METHOD PROVED; external production-grid price FITS.
At the same correction pair and 10240 cells, the two total prices are
183747.17913191413 and 157981.90712151656, below the pin 666472.585392.
These are externally enclosed prices. Lean proves the general bounding
method, not these full-grid numerical totals. Coefficient membership and
producer GO remain open; this record makes no RH claim.

What changes

Let c be the correction function, sigma the endpoint weight (+/-1/2),
and W(x) = exp(sigma*x)*c(x). Primes denote derivatives with respect to x.
The 2562 identity and coefficient-distance premise remain unchanged:

  exp(sigma*x)*c''(x) = W''(x) - 2*sigma*W'(x) + sigma^2*W(x).

Only the method for integrating norm(W'') changes. The old method uses a
constant cell bound formed from a signed midpoint plus unsigned variation.
Its unsigned third charge costs about 4.85 million at this grid (2573).

The new method connects the two endpoint values of W'' by a straight line,
called a chord. A second-derivative bound controls the distance from that
line. Since the function being bounded is W'', this curvature input is a
bound on W''''. For a cell [a,b] of width h = b-a and fourth bound M:

  integral_a^b norm(W'')
    <= h/2*(norm(W''(a)) + norm(W''(b))) + M*h^3/12.

The first term is the area of an endpoint trapezoid; the second pays for
bending away from the line. This removes the unsigned third term from
the second-integral channel. It does not discard a remainder or alter
coefficients. A bound on W'''' still applies throughout each cell.

```text
+--------------------------+     +-----------------------------+
| signed endpoint W''      | --> | endpoint trapezoid           |
+--------------------------+     +---------------+-------------+
                                                |
+--------------------------+     +---------------v-------------+
| whole-cell W'''' upper M | --> | add M*h^3/12                |
+--------------------------+     +---------------+-------------+
                                                |
                                +---------------v-------------+
                                | keep old first/value costs  |
                                +-----------------------------+
```

Lean proof chain

ConnesWeilRH/Dev/C1RouteACorrectionSecondChord2574.lean proves:

1. The unit-family fourth bound is nonnegative and valid across a cell.
   If the cell misses the support, the derivative is zero. A crossing
   cell uses the existing 2538 support-aware envelope.

2. The actual weighted correction's fourth derivative is bounded by the
   sum of (norm(center)+error)*unit-family bounds. Coefficient membership
   remains an explicit premise; it is not stored as an assumed conclusion.

3. normIntegralChordUpper2347 applied to W'' gives the cell integral bound.
   Signed endpoint center/error bounds replace the unknown endpoint norms.
   Adjacent interval integrals then sum to the composite bound.

4. externalPhysical2344_stripSecond_le_secondChord2574 combines this
   composite with the unchanged first/value composites from 2562/2539.

All six audited theorems compile and have exactly
[propext, Classical.choice, Quot.sound]. The paired Audit module lists
those six names. No new axioms or proof placeholders are introduced.

Same-run price

Command in a configured Linux workspace:
  python scripts/price_second_chord_grid_2574.py --cells 10240

The script first reruns both 2573 rows and requires every row field to
match exactly in the same process. It then prices signed W'' endpoints,
reuses the same-run fourth sum, and leaves first/value costs unchanged.
The mesh is h = 2*6.5536001/10240; the coefficient error is 1e-28.
This is the same owner, not a newly chosen coefficient vector.

```text
+------------------+------------------+------------------+
| charge           | sigma = -1/2     | sigma = +1/2     |
+------------------+------------------+------------------+
| W'' endpoints    | 125428.90464629  | 100344.09754020  |
| fourth remainder |  51792.09118786  |  51792.09118786  |
| second subtotal  | 177220.99583415  | 152136.18872806  |
| first            |   6503.31119667  |   5827.50058613  |
| value            |     22.87210110  |     18.21780732  |
| total            | 183747.17913191  | 157981.90712152  |
| pin              | 666472.585392    | 666472.585392    |
+------------------+------------------+------------------+
```

The remaining budget is about 482725.41 and 508490.68. The smaller
unsigned fourth remainder, rather than the removed third charge, is now
the main conservative addend. External prices use the coefficient
L1 magnitude (abs(real)+abs(imag)) as a safe upper for the complex norm.
Connecting that upper and the point enclosures to checked rational Lean
tables is still required.

Validation

scripts/validate_second_chord_grid_2574.py checks the exact h^3/12 charge,
all rational sums/margins, both signs, source hashes, predecessor identity,
and unchanged first/value costs. Seven corrupted artifacts are rejected.
With --reprice, a second full-grid run reproduces all non-timing fields
exactly; the committed control artifact records this gate as passed.
The validator reruns the independent 2573 derivative/reconstruction and
sample-envelope controls, and checks ten full signed endpoint aggregates
against independent mpmath differentiation, including support edges.
These samples do not constitute the full-grid table certificate.

Focused audit compilation succeeds (3725 jobs), the project root build
succeeds (4148 jobs), and all 22 record-2271 Linux integration tests pass.
The new files are outside the 2271 bound-input inventory; no bound source
was changed. Existing dependency style warnings are outside this patch.
The public build log is a focused module/audit excerpt with the full-log
SHA256 and the full-log error/placeholder scan counts; dependency replay
warnings are omitted from the excerpt.

Remaining obligations

1. Generate and kernel-check rational bounds for every required endpoint
   and fourth envelope, with explicit table-generation rounding allowances.
   Completion means Lean proves both full-grid numerical totals under the
   pin, not only the general inequality.

2. Prove that the actual exact interpolation coefficients meet the same
   center/error premise. Choosing arbitrary points in the boxes cannot
   satisfy this obligation.

3. Certify the base norm N(b), then connect both channels to the selected
   detector's remaining signed budget. Neither a favorable local price nor
   the present generic theorem establishes producer GO.

Evidence

  ConnesWeilRH/Dev/C1RouteACorrectionSecondChord2574.lean
  ConnesWeilRH/Dev/C1RouteACorrectionSecondChord2574Audit.lean
  scripts/price_second_chord_grid_2574.py
  scripts/validate_second_chord_grid_2574.py
  results/2574_second_chord_grid_10240.json
  results/2574_second_chord_controls_10240.json
  results/2574_chord_build.log
