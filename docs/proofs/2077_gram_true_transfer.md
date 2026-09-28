# 2077 - True Gram and a_mat transfer decomposition

Date: 2026-09-28.

Status: GRAM-AMATRIX-TRANSFER-GO-CANDIDATE.

A 45-digit independent Gram reconstruction was combined with the true
Laplace `a_mat` reconstruction. The largest Gram entry gap is
`4.966463632224165e-36`; the Frobenius gap is `1.1534324547973774e-35`.
Using the same owner and finite-window evaluator, the Q transfer prices are:

```text
Gram only       2.390883203125e4
 a_mat only     4.194993408203125e4
both            2.7311158203125e4
```

Each is below `1.3e-8` of the sampled negative margin. The result shows that
neither Gram nor `a_mat` is acting as a hidden cancellation crutch in the
stored model.

Decision: `GRAM-AMATRIX-TRANSFER-GO-CANDIDATE`. Formal interval enclosures and
the remaining COVER/uniformity layer are still required.

Artifact: `results/2077_gram_true_transfer.json`.
Script: `scripts/routea_gram_true_transfer_2077.py`.