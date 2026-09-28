# 2075 - Aggregate Euler-Maclaurin forward-error bound

Date: 2026-09-28.

Status: EM-JET-FORWARD-BOUND-CANDIDATE.

The 2074 panelwise jet calculation was repeated with analytic global
majorants for the shifted-Stirling sigma derivatives and an explicit IEEE
summation allowance for the finite prime cosine aggregate. At panel width
`0.002`:

```text
fourth-derivative L1 forward bound = 7.578168657527202e22
EM remainder forward bound          = 1.6840374794504895e9
remainder / L2 charge               = 0.03816761565740407
remainder / sampled margin          = 0.000494425376237464
```

The prime cosine summation gamma is `1.8285373215579673e-13`; the largest
center allowance among kernel derivatives is `0.017693258277074814`. The
forward-error allowance changes the 2074 remainder by only about `7.4e3`, so
floating-point summation is not the binding issue.

Decision: `EM-JET-FORWARD-BOUND-CANDIDATE`. This is the strongest finite-window
numerical route so far, but the IEEE model still needs to be replaced by an
exact certificate interface, and the stored owner coefficients must be
transferred to the actual physical owner. The remaining named model-to-real
obligations are the `a_mat` idealisation gap, the Gram rule gap, and COVER.

Artifact: `results/2075_finite_window_em_forward_bound.json`.
Script: `scripts/routea_finite_window_em_forward_bound_2075.py`.