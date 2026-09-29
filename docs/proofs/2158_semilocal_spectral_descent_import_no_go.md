# 2158 — Semilocal spectral-descent preprint is not a Weil-sign supplier

Date: 2026-09-29.

Status: EXACT ALGEBRAIC IMPORT NO-GO for the stated semilocal spectral
descent. This does not refute RH or every possible semilocal mechanism.

## Source and intended consumer

Christian Franchi Viceré, *A Proof of the Riemann Hypothesis for the
Riemann Zeta Function: Weil Positivity via Semilocal Spectral Descent*,
Zenodo record 19546495, v1 (12 April 2026), especially PDF pp. 3–4,
Theorems 1–3:
<https://zenodo.org/records/19546495>.
Its main cited source is Connes–Consani–Moscovici, *Zeta Spectral
Triples*, arXiv:2511.22755, Theorem 1.1 and §8:
<https://arxiv.org/html/2511.22755v1>.

The proposed consumer here would be the healthy `CompactLog` B5 route:
prove `QW(g)>=0` for the exact selected detector and its support-derived
finite visible-prime owner, then contradict its formal `QW(g)<0`. Current
assumptions are only the cited published finite spectral results, not RH
or positivity of the restricted Weil form. Failure is a missing sign or
owner identity at that interface.

## The algebraic gap

The cited CCM Theorem 1.1 starts with the smallest eigenvalue `epsilon_N`
of the truncated Weil form `QW_lambda^N`. Its part (i) uses the inner
product induced by `QW_lambda^N - epsilon_N I` on a quotient; it assumes
that this eigenvalue is simple and its eigenvector even. Part (iii) then
puts the zeros of the Fourier transform of that eigenvector on the real
line, as the spectrum of a constructed self-adjoint operator. CCM §8
explicitly lists the simple-even condition and convergence toward zeta
zeros as missing steps.

Subtracting the minimum eigenvalue always makes a Hermitian form
nonnegative, irrespective of the sign of the original form. The exact
two-dimensional counterexample is

```
Q = diag(-1, 1),   epsilon_min = -1,
Q - epsilon_min I = diag(0, 2) >= 0,
but Q(e_1) = -1 < 0.
```

Thus reality of the constructed spectral zeros and positivity of the
shifted quotient form do **not** imply `QW_lambda^N >= 0`. The Zenodo
preprint's Theorem 2 inserts an arithmetic-spectral equality that would
turn its real spectral zeros into a nonnegative sum of squares for the
**unshifted** Weil form. The cited CCM Theorem 1.1 supplies no such
sign-preserving equality; the `epsilon_N` shift is exactly the missing
term. The preprint's Theorem 3 notes that compact support sees finitely
many prime terms as the place set expands. That stabilization does not
repair the missing finite-level sign: a stable negative value remains
negative.

## Owner and provenance verdict

No theorem in the audited source supplies `QW(g)>=0` for the selected
`CompactLog` detector or identifies its exact finite visible-prime
functional with an unshifted positive spectral sum. The preprint therefore
cannot be imported as the missing C3'/B5 sign. Its DOI/timestamp and four
numerical examples establish provenance and samples, not this implication.
The CCM source was already present in the full-repository ledger; the
Zenodo bare identifier `19546495` had no full-repository `git grep` hit
before this record. This is a scoped source-interface no-go, not a claim
about the truth of the theorem if another proof is supplied.

Intake screen: TRUNC fired on the phrase "truncated Weil form". Record
2044's exhibit concerns a truncated lattice/book being read as the full
owner. This audit does not make that inference: it fails already at the
finite form's shifted-versus-unshifted sign. The complete-owner mismatch
would be a separate additional obligation if that sign were supplied.
