# 1211 - Projection cutoff fixed-response trace obstruction

Date: 2026-09-06.

Status: formal conditional no-go. RH is not claimed.

The projection-window cutoff operator remains positive and trace class at each
stage.  However, suppose its remainder-corrected trace readback converges to
the finite same-owner `qw`, while the insertion defect's real trace tends to
zero and the arithmetic response is fixed.  The exact three-owner trace
identity then makes the window-to-response defect bounded.  The existing
cofinal unbounded-trace theorem makes the same defect unbounded for every
nonzero detector.  Contradiction.

Therefore the live projection route must retain a divergent counterterm in
the insertion trace, or use a genuinely moving/renormalized response.  Operator
norm convergence of the insertion defect alone does not supply this trace
convergence and is not enough to trigger the no-go.

Evidence: `not_projectionCutoffLimitContracts_of_fixedResponse_and_traceDefect_vanishing`
in `C1Stage3ProjectionContractObstruction`, audited by its paired audit module.
Focused build: `p2-projection-fixed-response-obstruction-11.log`, 3823 jobs,
success footer, zero `error:` lines, zero `sorryAx`; the audit reports exactly
`[propext, Classical.choice, Quot.sound]`.
