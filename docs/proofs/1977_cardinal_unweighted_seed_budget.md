# 1977 — Remove the weighted-derivative oracle from the cardinal budget

Date: 2026-09-25.

## Consumer, owner and acceptance

Owner: the exact `correction nodes seed y` of record 1958, usable as the
correction in `(selectedOwner base (correction nodes seed y) n).sourceTest`.
The live endpoint remains the same four-point span's signed determinant and
same-index spectral tail in map 106. No equality with an older choice-based
selector or gate sign for this explicit selector is assumed.

Immediate consumer: `l1Mass_correction_le` from record 1961. Its cardinal
mass input previously required the whole derivative ladder of the
exponentially weighted seed, separately for each node. The new inequality
proves that input from the unweighted seed alone, with an explicit exponential
factor. It also consumes the already proved low-order seed constants in the
full finite-node correction sum. This is a smaller quantitative obligation;
it is not a signed-margin result or an unconditional RH proof.

Assumptions: the actual finite node set, interpolation data, and seed support
in `[-B,B]`. Interpolation still needs the existing nonzero seed mass theorem.
Failure would be a failure of the same-test conjugation or of the budget
inequality. A large resulting envelope is only a limitation of the estimate;
it is not a determinant counterexample.

## Proven result

Write `E_a f(x) = exp(a*x)*f(x)` and `D_t f = f' + t*f`. The product rule gives

```text
D_t(E_a f) = E_a(D_(t+a) f).
cardinalRaw nodes f z
  = E_(-z)(shiftedProduct [t-z : t in nodes.erase z] f).
```

Both identities are proved as equalities of `CompactLogTest`, not just
equalities of transforms or numerical approximations. The original test,
support, node list and node-product denominator are unchanged. Conjugation is
elementary differential algebra; no originality claim is made for it.

Support stability and the existing exponential-weight mass bound then prove

```text
l1Mass(cardinalRaw nodes f z)
  <= exp(abs(Re z)*B) * ladderBound (derivOrderL1 · f) [t-z] 0.

l1Mass(correction nodes f y)
  <= sum_z norm(y(z)/(nodeProduct nodes z z * laplaceAt f 0))
       * exp(abs(Re z)*B) * ladderBound (derivOrderL1 · f) [t-z] 0.
```

There is no derivative of an exponentially weighted seed left in these bounds.
The absolute values here control construction cost only; they do not replace
the signed gate moments or prime/Archimedean cancellation.

`ladderBound_mono_on_needed_orders` proves that a list of length d, starting at
order m, only requires bounds at orders m through m+d. Thus the cardinal L1
budget needs through `card(nodes.erase z)`; for z in nodes this is N-1.

For `smoothSeed`, `smoothSeedBudget higher` uses the certified values

```text
L0 <= 4, L1 = 2, L2 = 8, L3 <= 787283385/10^7.
```

`l1Mass_correction_smoothSeed_le_budget` consumes those facts for the complete
correction sum. Its only remaining derivative hypotheses are
`derivOrderL1 j smoothSeed <= higher j` for `4 <= j < nodes.card`.
There are no low-order hypotheses or weighted-derivative hypotheses left.
The user-supplied higher bounds are explicitly hypotheses, not manufactured
data. No bound is asserted for them here.

As an unconditional small-list check, the proved three-shift bound is

```text
L1mass(D_a D_b D_c smoothSeed)
  <= 78.7283385 + 8*(|a|+|b|+|c|)
       + 2*(|a||b|+|a||c|+|b||c|) + 4*|a||b||c|.
```

It is a regression of the actual ladder using record 1976, not a substitute
for the complete target/prefix node set.

## Order and owner audit: next work

The source `healthyUnscaledTargetNodes rho` is the functional-equation orbit
union `{rho+1/2, 1/2, 1, 3/2}`. The correction must also cover the required
closed-ball zero prefix and route nodes, with target values taking priority
at collisions. It must not be replaced by the four orbit nodes alone. The
generic explicit interpolation construction has not yet been instantiated
with that full union and priority rule; this record does not pretend to do so.

For any chosen complete set of N distinct nodes, this L1 budget requires
orders through N-1. Additional derivative decay estimates require their own
order accounting; the present theorem alone does not produce C2 or C4.
The shift by half-density, seed rescaling, nonzero mass, node separations,
base contraction and admissibility are still separate obligations.

Next: fix the full source node union and priority rule, then price the
remaining finite orders and node separations for that construction. Only
after the actual owner/readback and decay costs are available should a probe
test the determinant and relative tail jointly. Do not spend further effort
tightening the third-order decimal bracket without an error budget requiring
it. No signed determinant or same-index tail premise has been removed here.

## Evidence and documentation corrections

Source: `ConnesWeilRH/Dev/C1ExplicitCardinalSeedBudget.lean`.
Paired import/axiom probe: `C1ExplicitCardinalSeedBudgetAudit.lean`.
Focused build: `build-logs/1977_cardinal_seed_build5.log`, footer
`Build completed successfully (3656 jobs)`, zero lines beginning `error:`,
zero `sorryAx`, nine axiom records all exactly
`[propext, Classical.choice, Quot.sound]`, no warnings in either new module.
The paired audit is also the import-facing probe. Dependencies replay existing
style warnings; no claim that the whole repository is warning-free is made.
Route/Dev batch: `build-logs/1977_route_dev_batch.log`, footer
`Build completed successfully (3872 jobs)`, zero error lines and `sorryAx`;
all 15 printed axiom records use exactly the standard trio. Targets:

```text
lake build ConnesWeilRH.Dev.C1ExplicitCardinalSeedBudgetAudit
           ConnesWeilRH.Dev.C1FourPointMainlineRH
           ConnesWeilRH.Dev.C1FourPointMainlineRHAudit
           ConnesWeilRH.Route.CC20RouteRealization
```

The owning build targets the new module and its paired Audit. Builds run with
the resource-aware runner in the WSL ext4 mirror after syncing only edited
Lean files and verifying their SHA-256 hashes. The root aggregate check is
`lake build ConnesWeilRH`; its result is recorded below. The
root does not import every Dev leaf, so it supplements rather than replaces
the explicit new-module/import audit and Route/Dev batch.

The first root attempt (`1977_root_aggregate.log`) exposed an existing
destructuring error in `Source/CC20Concrete/HaarMellinMismatch.lean`: the bump
supplier returns nonnegativity, an upper bound, real-valuedness and a point
value, but the consumer omitted one component. Consequently `hvalue` was a
conjunction, not an equality. Windows and mirror hashes of the untouched file
agreed. The one-line repair binds `_hupper` and `_him` separately, preserving
the original theorem and proof. This is compatibility maintenance of an
existing obstruction, not new work on the frozen normalized producer.

Repair validation: `build-logs/1977_haar_repair_audit.log`, successful 3630-job
build of `ConnesWeilRH.Source.CC20Concrete.HaarMellinMismatch` and
`ConnesWeilRH.Dev.HaarMellinMismatchAudit`; both audited theorems use exactly
the standard trio. Final root: `build-logs/1977_root_aggregate2.log`, footer
`Build completed successfully (4148 jobs)`. Both logs have zero `error:` lines
and zero `sorryAx`. Existing dependency warnings are retained.

Records 1974--1976 and map 106 now distinguish an implicit expression from a
proved transcendental number. No transcendence theorem was supplied. The
reversed `(x_d,x_c)` interval is corrected to `(x_c,x_d)`, and record 1976
distinguishes its formal bracket crossing theorem from the unexported
single-peakedness / exact peak-value identity. Historical commit subjects
are not rewritten.
