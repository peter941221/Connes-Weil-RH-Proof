# Plan 022 Shifted-Mobius Frame First Verdict

Date: 2026-07-11

Verdict: **worth deeper research; not proved and not rejected.** A fixed family
of eight explicit moment-zero shifted-Mobius block directions survives every
rejection test through `N=4096`. It removes the projected Schur energy from the
proposed certificate and replaces one signed numerator by an eight-dimensional
positive correlation energy.

The decisive new identity is

```text
sum_k a_(N,d)(k)/k=0
  -> b_(N,d)(n)=0 for every n<=N.
```

The conservative certificate uses `||b||`, not `||(I-P_N)b||`. Consequently it
is a genuine lower bound for the decrement available after old-space
projection and does not hide the old Schur inverse in its denominator.

At the largest independently checked scale:

```text
N=4096
cutoff=250000
D=8
log(N)*conservativeCapture/d_N^2 = 0.16571703697830328
frame min/max eigenvalue ratio  = 0.009027591316103183
first-N coordinate maximum      = 2.1141942363467336e-17
normal-equation residual        = 7.819018000929052e-12
```

This is materially stronger than Plans 020--021 numerically and structurally:

```text
020: one signed direction + projected Schur energy
021: exact local cancellation + expanding future-multiple pollution
022: fixed finite frame + exact initial gap + unprojected conservative energy
```

The remaining bottom is still serious. One must prove a uniform positive lower
bound for the aggregate correlations with the optimal residual without
expanding that residual through the inverse old Gram matrix. Until that finite
divisor-sum theorem exists, Plan 022 is a research candidate rather than an RH
route.
