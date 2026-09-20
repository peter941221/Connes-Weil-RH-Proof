# 049 — Route map after 1741: window face adjudicated, converse oracle formal

Status line: the window face of P2 is now a MEASURED negative (λ_top ≈ −0.86
at the Yoshida window, four-engine verified through K = 128) and the reverse
arrow `SourceRH ⟹ window arch ≤ 0` is a committed Lean theorem on standard
axioms.  The falsifier oracle is formal in both directions; the class tested
so far is deeply on the RH side.  Everything else from map 048 is unchanged.

```text
  [tower, unchanged]
     off-line zero ⟹ qw(g) < 0  [formal]
        ⟹ 0 ≤ qw(g)  [OPEN GATE — premise P2]
        ⟹ RH

  P2 splits by class:
     full triple class : arch + finite ≤ 0   -- prime book is the obstacle (1740)
     window slice      : finite = 0, arch ≤ 0 alone
        |
        +-- ADJUDICATED (1741): λ_top(triple, w = log2/2) = −0.8619
        |   K-ladder 24→128 converging ≈ −0.86, four-engine verified,
        |   n-stable.  Window face HOLDS.  Falsifier unfired.
        |
        +-- FORMAL BOTH WAYS (1741):
            RH ⟹ arch ≤ 0 on window class   (C1SourceRHWeilConverse.lean,
                                              standard axioms)
            one positive smooth triple test ⟹ ¬RH   (contrapositive)

  width laws (1741, corrected denominator):
     triple crossing w* ≈ 0.83–0.85   (log5 < 2w* < log7)
     mass   crossing w₀ ≈ 0.39–0.40   (log2 < 2w₀ < log3)
     Yoshida w = 0.3466 sits deep inside the negative region.

  widening price (EXT-b): arch + finite ≤ 0 holds on the top eigenvector
  through w + 0.20; the prime-2 term turns positive first (+0.245).
```

Standing bones after this wave (unchanged unless noted):

* **Base** (carrier nonemptiness / Hardy clause at p = 2): OPEN, unchanged.
* **T4 / B4 / S3 / WO legs**: OPEN, unchanged.
* **Prime book** on the full triple class: OPEN — now with a measured
  on-ramp: the window route stays legal at least through `w + 0.20`, and
  fails (arch alone) only beyond `w* ≈ 0.83`.
* **Instrument frontier** (new): the smooth-basis adjudicator is trusted to
  K ≈ 128; pushing to K ≥ 256 is the next instrument task.

Reading order for this wave: `docs/proofs/1741_window_face_adjudication_and_weil_converse_oracle.md`
(errata E-A..E-D, σ identity, adjudication, Lean brick, EXT scans, laws
F74–F78), then `results/1741_window_adjudicator_results.json` and
`build-logs/1741_window_adjudicator.log` for the raw numbers.

Stop word unchanged: gate certificate.  RH not claimed.
