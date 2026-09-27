# Record 2042 — literature audit: Helson matrices, and a probabilistic reading of Weil sums

Date: 2026-09-27.

Status: two one-page abstract-level audits from the 2039-2041 desk batch.
Both PARKED — no route registered, no same-owner consumer named, no RH
claim. This record exists so the two candidates are never re-litigated
without new evidence.

## 1. Helson matrices (arXiv:1611.03772, "On Helson matrices: moment
problems, non-negativity, boundedness, and finite rank")

### 1.1 What the source proves

```text
Helson matrices: M(alpha) = {alpha(n m)}_{n,m >= 1} on l^2(N)
(multiplicative Hankel matrices). Main results (abstract level):

- M(alpha) >= 0  iff  alpha is the moment sequence of a measure mu on
  R^infinity, assuming alpha does not grow too fast;
- non-negative bounded Helson matrices correspond to moment measures that
  are Carleson measures for the Hardy space of countably many variables.
```

### 1.2 Audit verdict for this repository

The candidate attraction was: the prime-side quadratic form is
multiplicative-Hankel shaped, and the non-negativity dictionary (moment
sequences / Carleson measures) is an identity-class tool. The audit kills
the route on channel assignment:

```text
the prime channel  sum_k 2 Lambda(k)/sqrt(k) cos(2 pi xi log k)
is the Fourier transform of the POSITIVE discrete measure
  sum_k Lambda(k)/sqrt(k) (delta_{+log k} + delta_{-log k}),
hence positive-definite BY CONSTRUCTION — it is not the side that needs a
positivity theorem.

The signed channel is archimedean (the sigma/digamma local term), and it
is not multiplicative-Hankel shaped (it is the local factor at the
archimedean place, not an nm-indexed moment structure).
```

So the Helson dictionary characterizes positivity on the side the
repository already owns for free, and does not speak to the side that is
open. No same-owner consumer can be named (map 006 entry test fails).

```text
VERDICT: NOT ADMISSIBLE as a producer mechanism. Background dictionary
only. Do not re-open without a NEW bridge that realizes the archimedean
channel as a Helson/multiplicative-Hankel object.
```

## 2. A probabilistic interpretation of Weil's explicit sums
(arXiv:2311.08519, Morán Ledezma; listing updated through 2026)

### 2.1 What the source claims (abstract level)

Connects three paradigms: the adelic formulation of zeta, the Weil explicit
formula, and probabilistic number theory in the sense of Harald Bohr;
introduces "arithmetic spectral measures".

### 2.2 Audit verdict

At abstract level the paper is a paradigm-connection work. No unconditional
semi-local positivity theorem usable by this repository is visible at the
abstract level, and no statement identified as removing the same-owner qw
premise. This is exactly the pre-audit status Velez had before record 1995:
importable only after a full five-question audit, and the F67 trap
(any Weil-positivity-equivalent hypothesis) is the default failure mode for
this genre.

```text
VERDICT: ROUTE-C-STYLE AUDIT LANE ONLY, NOT SCHEDULED. Reading it is
optional background for Route E (record 2040) since both live in the
adele/Weil-sum world; it is not evidence and not an import.
```

## 3. Consequences

```text
Route H (Helson/multiplicative Hankel):   NOT REGISTERED (channel
                                          mismatch, Section 1.2).
Route C probabilistic companion:          PARKED (Section 2.2).
Live new routes after this batch: Route E only (map 109 / record 2040).
```

Evidence: arXiv abstracts as cited; committed kernel construction
(`scripts/fourpoint_owner_density_1959.py` sigma_vec + prime sum, the
same assembly as `routea_g8h_basis_comparison_2037.py` line 33-35).

No RH claim.
