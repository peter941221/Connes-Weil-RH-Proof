# 2121 - High-height owner budget crushes compact interpolation

Date: 2026-09-28.

Status: `SCOPED-NO-GO-FOR-ONE-NODE-PER-OWNER-INTERPOLATION`.

The project records the strict finite-height input that RH and simplicity are
verified through height `3 * 10^12`; any hypothetical off-line zero relevant
to the remaining proof must therefore lie above that floor. The earlier
`gamma≈39` stress family remains useful as an architecture diagnostic, but it
is not the real remaining owner regime.

At the lower edge of the remaining regime, using `N=0`, `delta=0.445`, and a
nearby zero-free Jensen center with `Re(c)=1.5`, the existing formal owner-count
interface translates as follows:

```text
gamma floor                         3.000e12
closed-ball radius                  3.000000000004e12
Jensen radius                       3.000000000004555e12
dyadic rung                         n = 40
xi growth exponent                  7.740561859544086e14
translated owner upper bound       1.116727020845884e15
largest compact family screened     62 nodes
upper bound / 62                    1.8011726142676e13
```

This is not a measured zero count. It is the current unconditional formal
upper-bound translation, using a conservative numerical placeholder for the
center xi norm; the exact Lean theorem retains the exact norm expression.
Nevertheless, it proves the architectural point: extending the compact
ladder one node per abstract owner zero cannot be the Go route in the actual
remaining height regime. The scope is narrow and explicit:

```text
CLOSED: one-node-per-abstract-owner-zero compact interpolation
       under the current Jensen/growth count interface.
OPEN:  owner-local signed constructions, local zero-density/spacing input,
       or a mechanism that does not interpolate the full closed-ball owner.
```

Evidence:

- `docs/proofs/1114_IC_problem_statement.md:131`
- `ConnesWeilRH/Dev/C1RouteAOwnerCardinality.lean:124`
- `results/2121_routea_high_height_owner_budget.json`
- `scripts/routea_high_height_owner_budget_2121.py`

This is not a global Route A no-go, not a producer theorem, and not an RH
claim.
