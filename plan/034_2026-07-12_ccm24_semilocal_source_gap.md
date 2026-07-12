# 034 CCM24 Semilocal Positivity Source Gap

Date: 2026-07-12

Status: source audit complete; no lower producer found.

## Finding

The original CCM24 paper proves the semilocal cyclic pair, the multiplier
measure, and the Hilbertian isomorphism

```text
theta_S : Sonin_lambda(infinity) -> Sonin_lambda(S).
```

It does not prove the fixed-test inequality needed by Plan 028:

```text
QW_S(g,g) >= Tr(C_S(g)^* S_S C_S(g))
```

nor a sign/ideal theorem for the finite-S post-`Q` remainder.  The introduction
describes semilocal Weil positivity as a program and defers a second semilocal
prolate candidate.

Source locations in `mainc2m24fine.tex`:

```text
186-201   positivity program and future-work statement
761-804   groundstate/cyclic-pair formulas
934-1032  Sonin stability and Hilbertian isomorphism
```

Primary source: `https://arxiv.org/abs/2310.18423`.

## Route Judgment

```text
Sonin domain transport: pass
semilocal positive trace: future-work proposal
finite-S remainder sign: absent
Plan 028: no source-backed lower owner
Lean implementation: forbidden
RH: unproved
```

The transport theorem may be used to state a future theorem, but not as that
theorem's sign premise. See proof 112.

