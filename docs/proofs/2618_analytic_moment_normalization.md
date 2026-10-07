2618: actual moment normalization and diagonal imaginary containment

Scope

The actual matrix is ownerMomentMatrix2351 capturedModulations2584
capturedNodes2584. Its row is a captured node; its column is a captured
family. No coefficient, modulation, node, interval, or support radius changes.

This record proves a finite-interval representation of every actual entry,
and proves the imaginary-coordinate containment for entry (0,0)
in the existing 2597 rectangle. It does not prove any complete rectangle
membership: the real-coordinate inequalities are still open.

1. Exact normalization

Let r = storedWidth(column)^2, z = capturedNodes2584(row), and m be the
captured modulation of the column. The physical coordinate is y; the
normalized coordinate is u = y/r. The original function vanishes outside
(-r,r), including at its endpoints. The normalized function vanishes outside
(-1,1), also including at its endpoints.

```text
Actual whole-line integral in y
             |
             | support containment (proved)
             v
Actual interval integral on (-r,r)
             |
             | y = r*u; r > 0 (proved)
             v
r * integral on (-1,1) of F(u)

F(u) = exp(-30/(1-u^2) + (z + m*i)*r*u), for |u| < 1
F(u) = 0,                                 otherwise
```

The factor r outside the integral is essential. The physical radius is the
square of the stored width, not the stored width itself. The theorem is
unconditional and is proved for all real modulations and complex nodes of
the 2351 system, not only at sampled positions.

2. Diagonal phase cancellation

For every captured diagonal index, z.im + m = 0 is an exact rational
identity. Thus z + m*i equals the real number z.re, and F is the complex
embedding of the real function

  exp(-30/(1-u^2) + z.re*r*u), for |u| < 1,

extended by zero. The integral is therefore exactly real, not approximately
real. Lean proves the imaginary part is zero for all 30 actual diagonal
entries. For entry (0,0), exact rational comparisons then put zero between
the existing 2597 imaginary endpoints, without an analytic-containment
hypothesis. The other 29 diagonal endpoint comparisons are not claimed.

The cancellation depends on the row-node/column-family pair. It is not a
claim that the complete matrix is real.

3. Precision target and remaining obligation

The exact 2351 witness gives the following interval widths for entry (0,0).
These describe stored data; they are not a new integral evaluation.

```text
+-------------------+---------------------+----------------------------+
| Coordinate        | Existing box width  | Actual containment status  |
+-------------------+---------------------+----------------------------+
| Real              | 1.19358002005e-64    | Not proved                 |
| Imaginary         | 1.11997064606e-420   | Proved via exact zero      |
+-------------------+---------------------+----------------------------+
```

The imaginary width is positive as an exact rational but underflows to zero
if converted to binary64. The validator uses rational subtraction and
decimal formatting, never binary64, for these readings. Its regression test
includes a positive width of 1e-420.

The next full-entry target is the two real inequalities for entry (0,0),
applied to the real normalized integral above. A numerical re-evaluation by
Arb would not discharge this Lean obligation. The implementation must prove
the integration error and point-value enclosures within the unchanged
2597 endpoints. The normalization alone supplies neither error bound.

4. Reproduction and audit

Use Linux, the repository lean-toolchain, a complete project library, and
matching Mathlib/package libraries. LEAN_PATH must begin with the complete
workspace project library; all other roots are explicit. No mounted fallback
is appended by the validator. WORKSPACE, LOGS, LEAN_BINARY, and LIBRARY_ROOTS
below are environment-specific parameters.

  LEAN_PATH="$WORKSPACE/.lake/build/lib/lean:$LIBRARY_ROOTS" python3 scripts/validate_analytic_moment_normalization_2618.py --workspace "$WORKSPACE" --logs "$LOGS" --lean "$LEAN_BINARY"

This compiles the three new modules under the resource-aware runner. Each
stage must exit successfully, produce an object, preserve its source hash,
and record its object hash. All 10 audited theorem leaves must report exactly
propext, Classical.choice, and Quot.sound. Upstream project and Mathlib objects
are reused; they are not freshly rebuilt by this command.

  python3 scripts/analytic_moment_normalization_selftest_2618.py

The seven tests cover tiny positive widths, exact subtraction, degenerate and
reversed widths, wrapped audit output, an added axiom, and an interrupted
process with a misleading success status. The machine-readable result is
results/2618_analytic_moment_normalization_validation.json.

The final warm-cache control compiled the three modules in 6.19 seconds
total compiler wall time, with a single-process peak RSS of 3.867 GiB.
This excludes upstream construction and earlier failed probes. The seven
2618 tests and the seventeen existing 2617 tests passed. No 2271 bound-input
source or manifest was changed, and no new 2271 integration run is claimed.

A proposed all-diagonal endpoint comparison timed out at both 200,000 and
2,000,000 heartbeats. Selecting the matrix row before unfolding its data also
timed out at the default allowance. These runs prove nothing and are not
retained as theorem sources. The final scope returns to one entry's endpoint
comparison under the default allowance; all 30 zero equalities remain proved.

5. Boundaries

There are 30 imaginary-zero equalities and one imaginary-coordinate
containment, but zero full analytic-entry containments. The remaining 899
imaginary-coordinate endpoint comparisons and all 900 real coordinates are
not certified by this record. The 2617 static
comparison remains at row zero only. Actual coefficient membership, the
selected-detector signed budget, producer GO, and RH are still open.
