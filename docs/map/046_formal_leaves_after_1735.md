# 046 — G8 mass-face formal leaves after wave 1735

Status: compressed fallback status. The mass-side kernel estimates below are
formal, but they do not prove the selected-detector sign. The sign face is
governed by [047].

## Formal assets

Wave 1735 and its follow-ups established reusable analytic leaves for the G8
mass channel:

- two-integration-by-parts decay and a squared-tail integral bound;
- a linear vertical-line bound for the digamma function;
- source-kernel pairing/readback on the Schwartz core;
- weighted-moment and annular-kernel estimates used by the conditional mass
  consumer;
- exact transport through the committed compact-kernel owner.

Representative modules are `C1G8R3AnnularTwoIBP.lean`,
`C1DigammaVerticalLine.lean`, and the associated source-kernel readback and
Audit leaves. Proof records 1734--1735 contain the theorem-level details.

## Boundary

These results control magnitude/decay. They do not supply:

- the same-owner signed gate certificate;
- the survivor S3 source-compressed energy of [042];
- the B4 composite commutator-root energy;
- `0 <= qw(g)` for the selected detector.

The historical paper claim that the mass face could be closed did not close
the gate's sign and index faces. Future use must name one of the current
producer consumers and prove the missing signed inequality, rather than add a
new tail or readback wrapper.

Classification: the listed leaves are `FORMAL`; any inference from them to
selected-detector nonnegativity remains `OPEN`.
