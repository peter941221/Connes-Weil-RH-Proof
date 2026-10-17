# Record 2731: source-function derivative jet semantics

Task card: owner = Real.smoothTransition on (0,1), with the exact
E=exp(-1/x+1/(1-x)) and R=1/(1+E) from record2730.
Premise to remove = unproved source-to-product derivative interpretation.
Consumer = record2730 derivative-bound replay, not an RH exit.
Completion = interior formula and derivative product recurrence in Lean,
standard-trio audit. Budget <=30 minutes, one module plus audit, one
thread, <=4GiB additional storage. Stop if proof needs new analytic
assumptions; no bulk interval replay. Endpoint and integration bounds
are outside this entry and remain open.


## Exact source identities

A derivative jet is the sequence of actual derivatives at one point:
slot k is the k-th derivative, without division by k!. This matches the
binomial coefficients used by the Python jet functions in record2730.
Let F(x)=-1/x+1/(1-x), E=exp(F), R=1/(1+E), T=Real.smoothTransition.
The new module proves, for 0<x<1 and every natural derivative order:

```text
T(x) = E(x) R(x)
T_n(x) = sum_(j=0..n) choose(n,j) E_j(x) R_(n-j)(x)
E_(n+1)(x) = sum_(j=0..n) choose(n,j) F_(j+1)(x) E_(n-j)(x)
R_(n+1)(x) = -sum_(j=0..n) choose(n+1,j+1)
              E_(j+1)(x) R_(n-j)(x) / (1+E(x)).
```

Here T_n,E_n,R_n,F_n mean iterated derivatives of the named source
functions, not arbitrary data. Denominator positivity follows from E>0.
The R recurrence is obtained by differentiating (1+E)R=1 and isolating
the zero-index term; it matches the reciprocal jet's division step.
Local smoothness of F,E,R is proved from 0<x<1, with no extra analytic
hypotheses. Source T is identified by its actual expNegInvGlue definition,
not by an asserted normalization or a numerically matched expression.

## Scope and remaining duties

This removes the paper-only source-to-product/exponential/reciprocal
recurrence gap. It is not a full proof of the Python interval evaluator.
The phase's reciprocal-input slots, bounds propagation, endpoint b/c/d
majorants, exact interval operation replay and integration partition
still require their own correctness arguments before D4<=1500 or
D7<=2e9 can be used as Lean facts. No wired pin is removed in this entry.

The order-n theorems apply in particular to orders four and seven.
No generic unrelated exit theorem or new zero model has been added.


## Verification and reproducibility

Focused Linux-native build, LEAN_NUM_THREADS=1, resource runner:

    lake build ConnesWeilRH.Dev.C1SeedJetSemantics2731Audit

Footer: Build completed successfully (3652 jobs). Nine theorem audit
records each have exactly [propext, Classical.choice, Quot.sound].
No new-module errors or warnings. Existing dependency warnings are
unchanged. Both source copies match the reviewed source byte-for-byte;
both compiled objects exist and are newer than their source copies.
The readback checker passes all eighteen gates, including exact
line-anchored declaration/audit pins and source hashes.

    python3 scripts/check_seed_jet_semantics_2731.py --workspace WORKSPACE

WORKSPACE denotes the Linux-native verification checkout. The checker
writes `results/2731_seed_jet_semantics.json` with portable relative
source names, source/checker/log hashes and per-gate readings. Build
objects are retained because this is a shared Dev module, not a disposable
entry-local aggregate. Target filesystem remained at 289 GiB free.

Evidence: `ConnesWeilRH/Dev/C1SeedJetSemantics2731.lean`, its paired
`C1SeedJetSemantics2731Audit.lean`, the checker and result above.
The unchanged Mathlib source was checked before using its existing
iterated-derivative product rule; no new Mathlib API was assumed.
