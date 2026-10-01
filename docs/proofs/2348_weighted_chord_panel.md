2348 - Weighted chord-panel bounds for the corrected physical source

Date: 2026-10-01.

Scope

Record 2347 proved the generic norm-integral chord bound. This record derives
the curvature formula for the actual real exponential weight and specializes
the quadrature implication to correctedPhysical and its second derivative.
The numerical derivative constants and node inequalities remain explicit
hypotheses; they are not imported from Python or JSON.

Objects and derivation

Let F be the complex physical source, sigma a real strip coordinate, R its
support radius, and m0/m1/m2 bounds on the norms of F/F first/F second. A
weight changes how strongly each position contributes. Here the weighted
function is V(x)=exp(sigma*x)*F(x), with a positive real exponential embedded
in the complex numbers.

```text
V second = exp(sigma*x) * (F second + 2*sigma*F first + sigma^2*F)

M = exp(abs(sigma)*R) * (m2 + 2*abs(sigma)*m1 + sigma^2*m0)

stripNorm <= compositeNodeUpper + h^2*(2*R)*M/12
```

The first identity follows by two product differentiations. Triangle
inequalities give the derivative norm bound. On abs(x)<=R, sigma*x is at
most abs(sigma)*R, so monotonicity of the real exponential supplies the common
weight factor. This matches the algebra in get_panel_upper from record 2341.

The strip integral is over the whole real line. Its integrand vanishes outside
[-R,R], so the proof first restricts to that interval and then applies the
uniform-grid theorem. The grid identity cells*h=2*R is exact.

Actual owner specialization

The owner radius is the exact real square of storedWidth 4, not the rounded
strip-radius pin. The existing owner smoothness and exact support theorems
discharge those structural premises for arbitrary coefficient/modulation
vectors. The ordinary norm channel consumes bounds at orders 0/1/2. The
second-norm channel consumes orders 2/3/4; its support is inherited through
the derivative-support inclusions. No new owner or sampled sigma grid is used.

```text
correctedPhysical              -> orders 0,1,2 -> stripNorm bound
correctedPhysical second       -> orders 2,3,4 -> stripSecondNorm bound
exact storedWidth 4 squared    -> common support and exact grid length
finite weighted node uppers    -> composite trapezoid upper
```

The two source-specific theorems are
correctedPhysical_stripNorm_le_nodeUpper2348 and
correctedPhysical_stripSecondNorm_le_nodeUpper2348.
They certify the implication from per-order derivative bounds and finite node
upper bounds to the actual continuous integrals, not the numerical premises
themselves. In particular the 2340 derivative ladder constants are not proved
by this record merely because their algebra matches the proved formula.

Validation

Focused Linux Lake build completes 3712 build-plan jobs. Ten audited leaves
have exactly [propext, Classical.choice, Quot.sound]. The new source has no
warnings and both Lean files match the Linux mirror by SHA-256. The unchanged
2341 and 2342 regression suites pass 11/11 and 15/15. Those tests preserve
instrument controls; they do not certify the numerical premises of the new
Lean theorem. No increased heartbeat option or disabled linter is introduced.

Evidence: results/2348_weighted_chord_panel_validation.json and
build-logs/2348_weighted_chord_panel_build_clean.log.

Remaining boundary

Exact ideal coefficient realization, bounds for the derivative ladder,
executed interval evaluator semantics and finite numerical node facts remain
separate obligations. No endpoint numerical inequality, healthy detector,
complete signed-kernel budget, live owner handoff, producer GO or RH is claimed.

Next steps

1. Prove the family derivative majorants through order four for the same bump
   and modulation conventions. A derivative majorant is an upper bound valid
   at every position, not only the nodes. Completion requires derived inequalities
   for the ladder constants, with all radius and coefficient factors retained.

2. Bind the exact repaired coefficients and certify the finite node inequalities
   on the exact rational grid. Completion is a proof-compatible certificate for
   the actual source, not a hash check or an extra endpoint-bound assumption.

3. Assemble the two endpoint norm facts and use the existing same-owner norm
   supplier, then return to the signed detector kernel budget. Norm control
   alone does not prove the selected functional sign.
