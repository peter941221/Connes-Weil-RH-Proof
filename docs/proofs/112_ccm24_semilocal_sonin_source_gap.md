# 112 CCM24 Semilocal Sonin Source Gap

Date: 2026-07-12

## Audit

The original CCM24 source (arXiv:2310.18423v2) was checked directly from
`mainc2m24fine.tex`.

The paper proves:

```text
theta_S maps the archimedean Sonin space into the semilocal Sonin space;
theta_S is a Hilbertian isomorphism of those Sonin spaces;
theta_S commutes with the Fourier transform;
the cyclic pair and semilocal multiplier measure are explicit.
```

The introduction states that using a semilocal prolate operator to handle Weil
positivity is a program, and that a second candidate for the semilocal prolate
operator is deferred to a forthcoming paper.  The source does not prove the
fixed-test inequality

```text
QW_S(g,g) >= Tr(C_S(g)^* S_S C_S(g))
```

nor a sign/ideal theorem for the finite-S remainder after `Q`.

The precise source locations are:

```text
mainc2m24fine.tex:186-201   stated positivity program, not a theorem
mainc2m24fine.tex:761-804   groundstate and cyclic-pair formulas
mainc2m24fine.tex:934-1032  Sonin stability and Hilbertian isomorphism
```

Primary source:

```text
https://arxiv.org/abs/2310.18423
```

## Consequence

The missing Plan 028 G2-B theorem is not a stale API wrapper.  It is a new
semilocal trace inequality.  The existing source only supplies the domain
transport needed to state it.  Building a Lean owner before proving that
inequality would store the desired sign as a premise.

## Verdict

```text
semilocal Sonin transport: source-backed
semilocal prolate positive trace: proposed/future work only
finite-S QW remainder sign: absent
Plan 028: still open mathematically, but no source-backed lower owner exists
Lean route owner: forbidden
RH: unproved
```

