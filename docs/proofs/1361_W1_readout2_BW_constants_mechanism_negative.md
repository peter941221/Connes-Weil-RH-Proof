# Record 1361 (W1 READOUT #2) - Bellotti-Wong constants parsed; correlation-mechanism scan returns NEGATIVE; TARGET-A2 stands as named open theorem; formal-reduction next

```text
+---------------------------------------------------------------------+
| Wave W1 continuation (1360 s5 queue items 1+2 executed). All        |
| constants parsed from primary text this session (arXiv:2412.15470v2 |
| HTML, question-scoped read). MODEL/REVIEW grade; RH NOT claimed.    |
+---------------------------------------------------------------------+
```

## 1. arXiv:2412.15470 (Bellotti-Wong, v2) - primary constants

Verbatim (Theorem 1.1, valid "for every T >= e"), with
|N(T) - T/(2pi) log(T/(2pi e))| <= C1 logT + C2 loglogT + C3:

| branch | C1 | C2 | C3 | sharper than |
|---|---|---|---|---|
| first estimate  | 0.10076 | 0.24460 | 8.08344 | prev. for T >= exp(447.981) |
| second estimate | 0.11200 | 0.12567 | 3.77417 | Trudgian [Tru14] for T > 387899 |

And their Theorem 1.2 gives an EXPLICIT WINDOW COUNT - the first
two-sided per-window occupancy certificate located with all-height
validity (window width 2):

    large range (T+1 > 30610046000):
      (1/pi - 0.201521) logT - min{0.4892 loglogT + 13.7861,
                                   3.3769 loglogT + 2.3884} - 1/25(T-1)
        <= N(T+1) - N(T-1) <=
      (1/pi + 0.20152) logT + min{... + 13.8633, ... + 2.4655} + 1/25(T-1)
    moderate range (3 <= T+1 <= 30610046000):
      (1/pi) logT - 5.66421 - ... <= N(T+1) - N(T-1) <= (1/pi) logT + 4.4798
    small-range S-difference: |S(T+1) - S(T-1)| <= 5.0334 (via Platt)
    and |S(T+1) - S(T-1)| <= 2.00001 C1 logT + 2.00001 min{...} large range

Bookkeeping: the 1360 s2 band stays on its Trudgian-1208.5846 S(T)
derivation (S(T) and N(T)-error are DIFFERENT objects; no conflation).
Impact on our numbers: (a) #9 constants row upgrades - logT coefficient
0.111 (S(T)) / 0.10076 (N(T) deep range); (b) the window theorem is a
better tool for any future LOCAL occupancy audit than the S(T) detour;
(c) also on record: they note an error in [Tru14] and a typo fix
(C3: 9.3675 -> 9.4925) in [HSW22] - the constants-drift law strikes
again (re-derive, never inherit).

## 2. Correlation-mechanism scan (1358 W1 s5 item 2): NEGATIVE

Question asked: does ANY located theorem take a hypothesis about
ON-LINE zero clustering (small A(I)) and output a conclusion about
OFF-LINE zero counts near 1/2? Audit by mechanism family:

| family | what it actually relates | usable for A2? |
|---|---|---|
| Deuring-Heilbronn repulsion | zeros of OTHER L-functions vs a near-1 zero of one L | NO - wrong half-plane, wrong object |
| Benli 2410.06082 (explicit DH) | same, quantitative, under Landau-Siegel | NO |
| density estimates N(sigma,T) | COUNT of off-line zeros, sigma bounded AWAY from 1/2 toward 1 | NO - no 1/2-neighbourhood windows |
| Montgomery/GGM pair correlation | on-line vs on-line, CONDITIONAL on RH | NO - one-sided limb, and RH-hypothesized |
| Rudnick-Sarnak / Bourgade | on-line statistics vs GUE, RH-hypothesized or averaged | NO |
| Granville-Sawhney / Conrey-Ghosh-Goldmakher, Bui et al. | EXISTENCE of small on-line gaps (upper-direction) | NO - opposite sign; and cannot even guarantee simplicity (1360 s3 row 1) |
| Levinson-Montgomery (zeta' off-line zeros) | multiplicity/cluster => zeta' zeros off line | NO - wrong target function, no off-line-zeta count |

Verdict: the mechanism inventory is EMPTY for the joint statement.
The physics intuition (clusters should repel) exists only inside
line-vs-line or half-plane-vs-half-plane pairs; the ON-LINE-CLUSTER
=> OFF-LINE-EXCLUSION arrow has no theorem attached to it anywhere
located. Per the 1358 pre-locked table this confirms OUTCOME 3's
consequence in its strongest form: TARGET-A2 (1360 s4) is not
derivable from located technology by any route we can name; the
A-route's remaining mathematical content IS A2 itself.

## 3. What we can still take (in-house, no invention of zeta math)

The attackable next object is the REDUCTION, not the theorem:
state A2 inside the formal tower and machine-check the implication
chain from A2 to the gate, so that the ONLY non-machine-checked
sentence between "someone proves A2 on paper" and "RH in Lean" is
the window-to-frame step (B2/B3, the C6 science). Design:

  1362 (next): define in Lean, from committed dictionary only
  (onLineZeroSet, offLineZeroSet, rightHalfOffLine, windows as
  ordinate intervals), the formal terms A_formal(window),
  N_off_nearline(window) and the hypothesis TargetA2; prove the
  NON-local parts (the pure contest algebra we already have: B4.1
  per-test form) lifted to the statement level, and REGISTER
  exactly which lemma (the frame gluing, C6) remains unformalized.
  No new analysis; definitions + bookkeeping of the wall.

Stop word unchanged: a green Lean certificate at the gate. Distance
readout tonight: mechanism table empty (row-certified, this record);
A2 has a formula, a scale (W = pi/log2, J ~ 0.05), constants
(0.111/0.10076 family), and from here the nearest formal milestone
is the 1362 reduction record - the missing zeta theorem itself
remains OUTSIDE what the campaign can currently reach, stated
plainly and without decoration.
