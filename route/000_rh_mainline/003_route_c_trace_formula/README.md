# 003 - Route C: trace-formula / Hilbert-space positivity

Status: LITERATURE AUDIT CANDIDATE. Not a producer route. RH is not claimed.

Hypothesis of the route:

```text
Weil quadratic form Q(f)
    -> identify Q(f) with a Hilbert-space norm or positive trace
    -> prove positivity for the full semi-local form
    -> Weil criterion
    -> Riemann Hypothesis
```

Why it is worth auditing:

- It attacks the sign obligation at the operator level instead of optimizing a
  finite detector.
- Connes' archimedean work gives a conceptual Hilbert-space/trace-formula
  mechanism.
- Recent finite-window work provides exact finite dictionaries and certified
  truncation budgets.

Why it is not currently more reliable than Routes A/B:

```text
archimedean positivity
    != full semi-local positivity
finite cutoff positivity
    != cutoff-free positivity without a complete tail theorem
numerical or preprint claim
    != audited theorem usable by this repository
```

Current status:

```text
FORMAL in this repository:
  none of the Route C positivity bridge

LITERATURE-BACKED:
  archimedean conceptual framework
  finite Guinand-Weil dictionaries and truncation budgets

OPEN:
  full semi-local positive operator / trace identity
  exact stabilization or limit passage
  compatibility with the project's actual CompactLog owner
  Lean consumer to SourceRH
```

Decision: keep Route C as a research candidate and literature-audit branch,
not as a third producer route. Promote it only if a source supplies a theorem
that directly removes the full semi-local positivity premise, or if a local
formalization closes that bridge for the same owner and quantifiers.

See:

- `001_literature_audit.md`
- `../004_common_bottleneck_audit/README.md`
- `docs/map/README.md`