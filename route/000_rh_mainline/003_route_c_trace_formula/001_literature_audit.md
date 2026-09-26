# 001 - Route C literature audit

Audit date: 2026-09-26.

This is an evidence record, not an endorsement of any claimed RH proof.

+------------------------------+------------------------------+------------------------------+
| Source                       | What it establishes          | Missing for Route C          |
+------------------------------+------------------------------+------------------------------+
| Connes, arXiv:2006.13771     | Detailed archimedean Weil     | Full semi-local positivity, |
| Weil positivity and Trace    | positivity framework using   | exact extension from the    |
| formula, the archimedean    | Hilbert-space compression,   | archimedean place to the    |
| place                        | Toeplitz and prolate tools.  | complete zeta form.         |
+------------------------------+------------------------------+------------------------------+
| Groskin, arXiv:2607.02828   | Exact finite Guinand-Weil    | Finite positivity is only a |
| A finite Guinand-Weil       | dictionary and an explicit   | certificate after its tail  |
| dictionary and archimedean  | two-sided archimedean-tail   | budget; this is not a full |
| tail order                  | certification rule.          | RH proof.                   |
+------------------------------+------------------------------+------------------------------+
| Zhu, arXiv:2608.24827       | Certified compact-window     | The paper explicitly reports |
| Weil positivity in compact  | positivity and two-sided     | that the one-stroke route   |
| windows                     | finite-window bounds.        | cannot reach RH unassisted  |
|                              |                              | because resolution becomes  |
|                              |                              | doubly exponential while   |
|                              |                              | the margin collapses.      |
+------------------------------+------------------------------+------------------------------+
| Velez, Zenodo 21184595 v5   | A preprint claims full Weil  | No independent verification |
| A proof of the Riemann      | positivity via Connes'      | or peer-reviewed audit was  |
| Hypothesis                  | semilocal trace formula and | found in the record; the    |
|                              | exact stabilization.        | key stabilization and       |
|                              |                              | positivity steps require   |
|                              |                              | line-by-line audit.         |
+------------------------------+------------------------------+------------------------------+

Source URLs:

```text
https://arxiv.org/abs/2006.13771
https://arxiv.org/abs/2607.02828
https://arxiv.org/abs/2608.24827
https://zenodo.org/records/21184595
```

Assessment:

```text
Route C has a genuine conceptual mechanism.
Route C does not currently have a verified full semi-local positivity theorem.
The compact-window evidence identifies a serious scale barrier.
The 2026 Zenodo claim is a lead for audit, not accepted proof evidence.
```

Audit questions before promotion:

1. Where exactly is the full semi-local Weil form defined and shown equal to
   the proposed Hilbert-space norm?
2. What theorem gives positivity uniformly after removing the cutoff?
3. What controls the archimedean, prime, and zero-side limits simultaneously?
4. Does the theorem apply to the project's actual owner and support, or does it
   switch to a different test-function class?
5. Can the claimed stabilization be formalized without assuming positivity in
   the statement or hiding it in an input certificate?

Until all five answers are sourced and checked, Route C remains audit-only.
Additional external-lead triage:

- Velez, Zenodo 21184595 v5 claims full Weil positivity and exact stabilization,
  but it is an open preprint and has not been independently verified here.
- Shimizu, Zenodo 21108581 v2.4 is an operator-theoretic lead, but its own
  record carries a disclaimer that the working draft contains fatal proof
  errors; it is not accepted evidence.
- Other self-described RH proofs are kept out of the route topology until a
  primary-source audit identifies a concrete owner-preserving theorem.
