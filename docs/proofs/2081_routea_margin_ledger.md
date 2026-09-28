# 2081 - Route A numerical margin ledger

Date: 2026-09-28.

Status: NUMERICAL-MARGIN-LEDGER-CANDIDATE.

For the one-copy G8-H sampled owner, the m=6400 finite-window reading is
`-3.406049851783499e12`. The currently priced terms sum to:

```text
L2 model charge             4.4122155666378555e10
finite-window EM forward    1.6840374794504895e9
a_mat transfer              4.194993408203125e4
Gram transfer               2.390883203125e4
tail 40..160 (measured)     4.091205950971527e6
tail 160..infinity           negligible
known error sum             4.581035021054613e10
known error / margin        0.013449700445975153
```

The residual sampled margin after these terms is
`3.360239501572953e12`.
This ledger is useful because it identifies the true remaining blockers rather
than hiding them in one total: uniform COVER, formal outward promotion of the
finite-window and matrix bounds, the physical-owner/model-to-real transfer,
and the symbolic tail proof. It combines candidates and measurements and is
not itself a producer theorem or an RH proof.

Artifact: `results/2081_routea_margin_ledger.json`.
Script: `scripts/routea_margin_ledger_2081.py`.
