# 024 Metric Sonin Projection And Fixed-S Remainder

Date: 2026-07-12

Status: rejected as an executable Plan 016 Contract M3B lane. The metric
projection remains a formal research idea, but the claimed compact remainder
and final Rayleigh problem are not defined on one common Hilbert space. No Lean
owner or route consumer is authorized.

## 1. Result First

```text
current result: rejected as formulated

direct fixed-S scalar remainder: rejected
cross-spectral prolate trace: rejected as active source-backed object
metric Sonin projection: bounded projection formula only
global fixed-S trace identity: unproved
post-Q compact remainder: unproved
de Branges Rayleigh gate: ill-typed
second prime-power coefficient: factor 2 too large
RH: unproved
```

The former completion gate was:

```text
For S={infinity,2}, prove on the common de Branges subspace

  C_route={F | F(0)=F(1/2)=F(1)=0}

that the fixed-S post-Q remainder is

  -2 Id+K_S,  K_S compact self-adjoint,

and

  <F,K_S F><2 norm(F)^2  for every nonzero F in C_route.
```

This is not currently a well-formed quadratic-form problem. CC20's post-`Q`
operator acts on `L2(sqrt I, d*rho)`, whose vector is the convolution root
`xi`. CCM24's `B_lambda` is the entire-function realization of the Sonin
space. No source or project theorem identifies these Hilbert spaces or
transports the fixed-`S` remainder between them. See
`docs/proofs/040_metric_sonin_domain_rejection.md`.

The later same-object expansion gives a stronger rejection. At order
`a^2=p^-1`, the endpoint metric projection has single-crossing coefficient
`a^2`; the crossing length `2 log(p)` therefore produces twice the CCM25
`p^2` Weil atom. The excess is noncompact. See
`docs/proofs/042_metric_sonin_second_prime_power_rejection.md`.

The lane may be reopened only after one same-object theorem supplies all of:

```text
fixed-S trace identity on a named test-root Hilbert space H_I
explicit post-Q kernel K_(S,I) on H_I
proof that every noncompact single crossing is exactly in the Weil main term
compactness/self-adjointness of the residual kernel
route Mellin conditions represented by named vectors in H_I
strict restricted Rayleigh bound in that same H_I norm
```

## 2. What Counts As Solved

```text
1. The same source test and convolution square occur in positivity and QW.
2. Metric Sonin projection is the positive-trace owner.
3. Every single crossing is read as the matching CCM25 prime-power atom.
4. All remaining Euler/prolate words form one explicit compact kernel on the
   test-root Hilbert space.
5. The strict bound holds on the route kernel intersection in that same space,
   without arbitrary bad-vector rows.
6. Plan 016 M3B consumes the theorem and the old fallback is inactive.
```

## 3. What Does Not Count

```text
finite-section prolate eigenvalue convergence
compactness without a sign/norm theorem
equivalent de Branges norms without bad-space ownership
arbitrary finite bad-vector conditioning
theta/eta dual pairing, which cancels Euler arithmetic
an axiom-clean wrapper storing the Rayleigh bound as a premise
```

## 4. Current Evidence

```text
docs/proofs/034_metric_sonin_projection_escape.md
  exact projection T_S R(R T_S* T_S R)^-1 R T_S*

docs/proofs/035_metric_projection_second_variation.md
  raw p^-1 identity cancels before read-off

docs/proofs/036_metric_projection_logarithmic_flow.md
  all U_p^m channels occur in the logarithmic flow

docs/proofs/037_metric_sonin_ideal_closure.md
  superseded: confuses the prolate angle correction with the post-Q kernel

docs/proofs/038_single_crossing_weil_read_off.md
  exact p^(-m/2)log(p) coefficient, same test, matching QW sign

docs/proofs/039_debranges_bad_space_gate.md
  superseded: places the post-Q operator on the wrong Hilbert space

docs/proofs/040_metric_sonin_domain_rejection.md
  source-line audit and exact reopening contract

docs/proofs/042_metric_sonin_second_prime_power_rejection.md
  same-object p^2 coefficient counterexample to the endpoint metric projection
```

Primary sources:

```text
CC20  arXiv:2006.13771, weil-compo.tex:1072-1076, 1100-1103, 2105-2120
CCM24 arXiv:2310.18423, mainc2m24fine.tex:946-1029, 1031-1073
CCM25 finite-prime formula and project sign audit used by Plan 016
```

## 5. Dependency Chain

```text
theta_S bounded Sonin isomorphism
  -> H_S=theta_S*theta_S
  -> R_S=theta_S R(R H_S R)^-1 R theta_S*
  -> positive one-sided Sonin trace
  -> single crossings = finite-prime QW atoms
  -> remainder = -2 Id+compact
  -> strict <2 bound on C_route
  -> Plan 016 M3B finite-S sign theorem
  -> existing restricted/full and final-sign consumers
```

## 6. Reopening Route

Do not create Lean declarations or run certified spectral sections before the
same-object fixed-`S` kernel theorem is proved on paper.

After that gate:

```text
1. Define one data-bearing metric Sonin owner for test, square, H_S, projection,
   positive trace, QW read-off, and remainder.
2. Prove projection positivity and trace-class legality.
3. Prove pointwise prime-power read-off before forming sums.
4. Prove the compact remainder equality and strict restricted Rayleigh bound
   on the same test-root Hilbert space.
5. Rewire Plan 016 M3B/M4 consumer; do not route through old cross-prolate data.
```

## 7. Static Rejection Scans

```powershell
rg -n "Pi_-.*Pi_+|crossSpectral|metricSonin|Set\.univ|\bTrue\b|sorry|axiom" ConnesWeilRH -g "*.lean"
rg -n "finitePrimeTerm.*=-|primePower.*sign" ConnesWeilRH docs -g "*.lean" -g "*.md"
```

Reject aliases such as `metricRemainderBound := desiredRayleighBound` or a
structure field that directly stores the final `<2` conclusion.

## 8. WSL Build Gate

Future smallest builds after a real Lean producer exists:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete.CompactBadSpace

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Route.RouteTheorem
```

No build is required for this index-only plan.

## 9. Focused Axiom Audit

Planned semantic targets, names to be fixed when the owning module exists:

```text
metricSoninProjection_eq_orthogonalProjection
metricSonin_singleCrossing_eq_finitePrimeAtom
metricSonin_postQ_remainder_eq_negTwo_add_compact
metricSonin_restricted_rayleigh_lt_two
```

For each target run `#check @name`, `#print name`, and `#print axioms name`.
Reject theorem parameters that contain the target sign or Rayleigh conclusion.

## 10. Final Acceptance Text

```text
Result: rejected as an executable lane; RH remains unproved.
Umbrella consumer: Plan 016 Contract M3B remains unfilled.
Old weak paths inactive: direct D_S and cross-spectral trace.
Candidate projection: metric Sonin orthogonal projection.
Missing owner: one explicit fixed-S post-Q kernel on the test-root Hilbert space.
Forbidden shortcut: moving that kernel to CCM24 B_lambda without an exact
same-object unitary transport theorem.
```
