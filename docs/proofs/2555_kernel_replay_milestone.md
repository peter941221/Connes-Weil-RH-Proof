Record 2555: faster kernel-checked replay on complete production nodes

Paired rational state equality now has a checked alternative using
decide +kernel. The selected input, approximate center, error radius,
derivative factor and analytic transfer are unchanged. This is kernel
reduction, not native_decide and not an extra trust assumption. The eight
complete support-ladder nodes from 2553 pass with the new strategy, covering
both sigma signs and 130 interior plus 110 exterior branches.

Generate with scripts/generate_kernel_trial_2555.py. The focused runner
scripts/run_kernel_trial_2555.sh compares four actual family transfers;
scripts/run_kernel_nodes_2555.sh checks the complete ladder. For same-run
node comparisons and integration, run
scripts/build_replay_milestone_2555.sh --matched under one heavy resource
lease. LEAN_LAKE may select the installed lake command. The runner invokes
lake env lean directly for timings, then builds the project root and all
2552-2555 modules. The 16-logical-CPU WSL environment runs timed variants
sequentially, with an import baseline first.

The four-family matched control reads 7.41 s elapsed / 17.97 s user CPU;
the kernel variant reads 4.68 s / 9.34 s. Full-node matched comparisons:

```text
+------------+--------------------+----------+----------+---------+
| benchmark  | shape              | before   | after    | delta   |
+------------+--------------------+----------+----------+---------+
| elapsed    | node2701, sigma-1/2 | 38.11 s  | 17.02 s  | -55.3%  |
| elapsed    | node5440, sigma+1/2 | 34.47 s  | 20.94 s  | -39.3%  |
+------------+--------------------+----------+----------+---------+
| user CPU   | node2701, sigma-1/2 | 146.13 s | 60.91 s  | -58.3%  |
| user CPU   | node5440, sigma+1/2 | 138.83 s | 64.70 s  | -53.4%  |
+------------+--------------------+----------+----------+---------+
```

Peak RSS falls from 6375228 to 4540816 KiB at node2701 and from 6307228
to 4580328 KiB at node5440. These are single matched readings, not a
statistical guarantee. The CPU reduction and unchanged payloads support
using the kernel strategy for subsequent node generation. They do not
establish the cost of untested grid positions or other proof channels.

Acceptance checks exact regeneration, independent exponent/factor arithmetic,
all support branches, standard axiom sets, and byte-identical project
dependency sources/configuration. The previous 2553 corruption tests and
accepted-payload comparisons remain separate anchors; the kernel sources
are exact identifier/tactic-only transformations of those checked sources.
Evidence: results/2555_kernel_trial_readback.json, plus records2552-2554
for the matched baseline, support ladder and cumulative cost diagnosis.

Integration initially reported line-length warnings after symbol renaming.
The final formatting pass preserves the complete whitespace-separated token
sequence in all 23 new Lean files; results/2555_layout_control.json records
before/after hashes and token identity. Timing readings refer to the
pre-format sources; final integration checks the token-identical formatted
sources. The exact rational reader now accepts a newline inside a rational
type annotation, with the previous 30-family replay retained as a regression
anchor. No bound, proof tactic or numeric payload changed in this cleanup.

Final integration completed 4561 build jobs. All 610 terminal declarations
from the new modules use exactly the three permitted axioms; 750 project
dependency sources match the verification environment byte-for-byte, and
the final new modules have no warnings. The layout control verifies all
23 formatted sources.

The milestone makes complete paired nodes cheaper to verify. The grid
still contains 640940 active shared endpoint/midpoint exponentials before
fourth-envelope and assembly costs. Next work should reuse endpoint
certificates between neighboring cells and between derivative orders,
assemble bounded segments, and then close the full-grid numeric sum.
Exact interpolation coefficient membership, correction channels and the
complete selected-owner signed budget remain open. No new whole-cell
coverage, full-grid certificate, producer acceptance or RH claim follows.
