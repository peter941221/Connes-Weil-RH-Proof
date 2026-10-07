Record 2622: ten actual moment panels batch-certified
Date: 2026-10-07

Result

The result is positive: the actual-panel consumer is parameterized by
panel index, and panels 90 through 99 of the committed 180-panel
partition - including panel 094 as a semantic control against the
committed 2621 certificate - now carry complete Lean-certified integral
error bounds. The validator emits
ACTUAL_PANEL_BATCH_INTEGRALS_LEAN_CERTIFIED after thirty-one serial
module builds and 260 audited leaves, each reporting exactly
[propext, Classical.choice, Quot.sound]. The other 170 panels,
partition assembly, and full (0,0) containment remain open; producer GO
and RH remain false.

The batch keeps the record-2621 shape unchanged: per panel, the scalars
module (26 scalar exponent certificates), the table module (polynomial,
residual, primitive, and replay theorems), and the actual-panel consumer
(integral certificate against the normalized [1/25,1/20] interval from
the committed partition), with panel 094's regenerated payload
byte-matching the committed 2621 payload. Partition pricing is carried
by the committed gate: the 180-panel charge sum 6.836687e-71 sits
inside the 2597 rectangle width 1.19e-64 with a factor-100 budget
(partition-sum, not a uniform per-panel bound - the per-panel charge
varies across panels and only the sum is required to fit).

What the parameterization changed and what it did not

The generator clones the compiled-good 2621 proof shape per panel,
substituting only the panel center and its certificates; consumer names
keep the 2621 conventions with the panel tag appended. The partition
pricing, the owner, the physical radius, the degree-32 truncation, and
the five-slot residual discipline are all inherited unchanged. The
semantic regression reconstructs every panel's coefficients with an
independent second engine and rejects perturbed coefficients,
perturbed primitives, inflated budgets, and huge phases; twelve tests
run green before and after the builds.

Two emitted-Lean defects were caught only by the compiler and fixed in
the generator, not in the artifacts: an unbalanced closing paren in the
negated half-width literal of the integral replay theorem
(polynomialEvalRat2621 (-1 / 200)) is term-distinct from
(-1 / 200)), and a missing : ℝ annotation in the Set.uIcc_of_le probe
let 1 / 200 elaborate outside Real where the rewrite target cannot
match. Python-side gates (semantic recomputation, byte fingerprints,
LF checks) cannot catch either class; the first batch module's compile
is the syntax gate, and generated theorem shapes must be checked
against the compiled-good template when a generator clones one.

Build and validation facts

Thirty-one modules compile serially through the resource runner with
the pinned v4.30.0 toolchain and workspace-local Mathlib packages; the
total compiler wall time is 60 seconds with peak RSS 4.0 GiB. The
workspace practices are now binding: a verify workspace must carry the
lean-toolchain pin (the runner cds into the workspace; a toolchain-less
cwd makes the elan shim resolve the default toolchain, and a newer
compiler rejects every pinned object with "incompatible header"), and
new workspaces seed from the most recent all-Linux-built library, not
from the mixed-provenance promoted tree.

The validator re-checks generated sources and payload drift before and
after the runs, re-hashes every inherited and new source/object at the
end, and requires the certified 2621 prerequisite to remain
fingerprint-fresh. The partition assembly and the actual (0,0)
containment remain explicitly uncertified.

Primary evidence:

  scripts/generate_moment_panel_batch_2622.py
  scripts/moment_panel_batch_selftest_2622.py
  scripts/validate_moment_panel_batch_2622.py
  ConnesWeilRH/Dev/C1RouteAMoment*2622Panel*.lean (30 modules)
  ConnesWeilRH/Dev/C1RouteAMomentPanelBatchAudit2622.lean
  results/2622_moment_panel_batch_payload.json
  results/2622_moment_panel_batch_validation.json

Reproduction interface

Run scripts/validate_moment_panel_batch_2622.py in Linux with
--workspace pointing at a toolchain-pinned, Linux-built workspace
library and --logs at the log directory. The validator requires the
certified 2621 objects, regenerates and byte-checks the batch, runs the
twelve selftests, builds the thirty-one modules, audits all 260 leaves,
and re-verifies every hash at run end before emitting the status.

Next steps

1. Generate and certify the remaining 170 panels in larger batches; the
   per-panel cost is now measured at roughly five seconds of compiler
   wall time, so batch size is bounded by validation discipline, not
   compute.

2. Assemble the 180 certified panels plus the two certified edges into
   the partition theorem, joining with 2618's exact imaginary zero to
   close the actual (0,0) rectangle containment.

3. Open the off-diagonal lane per record 2624's pricing: complex scalar
   engine first, then the pilot entry (0,3) at degree 55.
