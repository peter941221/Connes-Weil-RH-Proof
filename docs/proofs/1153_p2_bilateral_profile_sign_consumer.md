# Record 1153 — P2 bilateral-profile sign consumer

Date: 2026-09-06

## Result

`C1P2BilateralProfile.lean` now contains the direct same-owner sign bridge

```text
archimedeanTerm(g□) ≤ 0
and  Re(g□(log n) + g□(-log n)) ≤ 0
     for every visible prime power n
      ⟹ qw(g) ≥ 0.
```

The finite-term coefficient is formally the nonnegative real weight
`Λ(n)/√n` times the bilateral profile.  Therefore profile nonpositivity gives
each finite term and the complete visible-prime sum nonpositive; the healthy
triple-vanishing Weil identity then gives the displayed `qw` sign.

The first attempt exposed and was corrected for the sign direction: profile
nonnegativity would make the finite-prime contribution nonnegative and hence
would not imply `qw ≥ 0`.  The landed theorem uses only the mathematically
correct nonpositive profile premise.

The owning and audit modules build successfully in 3660 jobs.  All audited
declarations use `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.

## Route meaning

This is a FORMAL detector-specific consumer and a sharper producer contract.
It does not prove either sign for the pinned orbit detector, does not invoke
ROOT positivity, and does not claim RH.  P2/C3 remains OPEN: the missing work
is now an archimedean nonpositive estimate together with visible bilateral
profile nonpositivity on the same healthy orbit owner.
