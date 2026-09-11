# Record 1336 — C4 memo: what a zero-carrying carrier would have to be (analysis only)

Date: 2026-09-11.
Status: DECISION MEMO commissioned by record 1335 section 5 option M.
Pure analysis. No Source-layer change, no Lean brick, no probe executed,
nothing in this record is self-authorized for implementation. RH is not
claimed.

## 1. The defect to repair (from records 1334-1335)

The committed carrier `W = {w in H^2(C+) : phi w in H^2(C-)}` with the
Gamma-only phase has kernel directions equal to the symbol winding
`|W(L)| ~ 2 L log L` (the Fredholm index, verified to 0.5%), and the
measured corridor capacity of that sector is the generic value
`A_tau = 1.995 - 2.012` for every prime lag: no exclusion, no hiding,
`hcolumn` impossible (record 1335). The pipe is full of non-antiperiodic
junk because **the model contains no zero data at all**.

## 2. The naive upgrade is identically wrong — record the trap

The tempting C4 reading, "put zeta into the scattering phase", fails as a
meromorphic identity:

```text
Phi(1-s) = Phi(s)          (completed functional equation)
Xi(s) := Gamma-part(s) * zeta-part(s),   Xi(1-s) = Xi(s)
  =>  zeta-part(1-s)/zeta-part(s) = Gamma-part(s)/Gamma-part(1-s) = phi(s)^{-1}
  =>  phi * (zeta ratio)  ==  1   identically.
```

Multiplying the symbol by any zeta/xi quotient either cancels the phase to
1 (killing the model: then `W = {w : w in H^2+ cap H^2-} = {0}`) or leaves
it unchanged. **Zero information cannot enter through the symbol; the
symbol only knows the Gamma part. It must enter as constraints on the
carrier elements.** (This is also, in one line, why de Branges-style
"phase engineering" programs are space-theoretic, not symbol-theoretic.)

## 3. The right C4 shape: zeros as vanishing constraints

Definition sketch (to be preregistered separately if funded):

```text
W_zero(lambda) := { w in W(lambda) :  w(xi_n) = 0 for every committed
                   zero rho_n = 1/2 + i gamma_n mapped by xi_n = gamma_n/(2pi) }
```

Why this is the Sonin/Weil space: Weil's own nonzero witnesses
`Lambda(x+a)Lambda(x+b)` (record 1331 section 2 citation) live in exactly
such an intersection - entire functions satisfying the Gamma model-space
growth AND vanishing at the zero lattice; their nontriviality is the
explicit-formula content, not a symbol trick.

Index bookkeeping (the mechanism that repairs record 1334): the Riemann-
von Mangoldt counting identity in phase form is

```text
N(T) = theta(T)/pi + S(T) + 7/8 + o(1),
```

where `theta` is exactly the archimedean phase integral (the smooth
winding measured in record 1333/1334) and `S(T) = pi^{-1} arg zeta(1/2+iT)`
is the fluctuation. Imposing the `N(T)` point vanishing on the
`theta/pi`-dimensional index sector cancels the Gamma winding to leading
order; the surviving truncated carrier dimension is `O(sup|S|)`-scale:
thin, and its growth rate is itself zero-distribution information
(under RH-type control `S(T) = O(log T / log log T)`; unconditional
omega-results make it larger - the memo flags this as RH-adjacent
behavior WITHOUT any claim). The corridor capacity question then becomes
well-posed: does `S`-sector mass concentrate in the prime-log lattices —
this IS record 1329 section 8's necessary condition, now with its input
(a zero list) defined.

## 4. What the program already owns (inventory for costing)

```text
+------------------------------+------------------------------------------+
| need                         | repo status                              |
+------------------------------+------------------------------------------+
| entire xi + functional       | DONE: completedRiemannXi                 |
| equation                     | (Source/CC20ZetaCounting.lean:31),       |
|                              | completedRiemannXi_one_sub (:257),     |
|                              | folding/norm variants (:266-:296)      |
| zero data with certified     | PARTIAL: off-line zero identities live   |
| locations                    | at the tower level; CC20YoshidaNearZeros |
|                              | + interval certifier (law-34, records    |
|                              | 1087-1114) provide certified boxes; a    |
|                              | usable xi-lattice list per record is     |
|                              | NEW work (bounded: certifier exists)     |
| point evaluation on W        | MISSING: needs the record-1331 G2 strip  |
| (to state the constraints)   | RKHS package — G2 now has its first      |
|                              | CONSUMER (1331's "no consumer" verdict   |
|                              | is superseded by this memo)              |
| HT involution + support      | UNCHANGED: the phase stays Gamma-only;   |
| geometry                     | 1267/1330/1331 structure survives under  |
|                              | intersection (subspace of RKHS keeps     |
|                              | continuous kernel, K_up <= K)            |
| frame chain 1269-1330        | RE-PARAMETERIZATION: 51 bricks are       |
|                              | stated over finiteSCarrier/range frames; |
|                              | swapping to W_zero needs either a        |
|                              | generalized carrier parameter or a       |
|                              | parallel chain — the dominant cost item  |
+------------------------------+------------------------------------------+
```

## 5. What C4 buys and what it does NOT buy

Buys: (a) a carrier whose nontriviality is the classical Weil witness
fact (G1 acquires a construction route); (b) a satisfiable-feeling
`hcolumn` — the premise stops being provably false; (c) the tower's
off-line zeros acquire a consumer INSIDE the carrier, wiring the
dependency tower's first link to G8 for the first time; (d) G2 acquires
its consumer, ending the 1331 hold rationale for G2.

Does NOT buy: (a) any proof that the upgraded `hcolumn` HOLDS — that is
the explicit-formula capacity question (1329 section 8), open analytic
research with prime-correlation-of-zeros content; (b) the G8 P3
contradiction engine is not restored automatically: on the Gamma-only
model the premise is now known false, so the engine must be rebuilt on
`W_zero` and re-gated from P0; (c) no RH statement anywhere.

## 6. Costed decision options (for the owner; none executed)

```text
M1 (paper, ~days): write the W_zero prereg + the index-cancellation
    numerical check (truncated vanishing vs winding: expect dim ~ O(S));
    fully in the 1332-1335 instrument set, no Lean.
M2 (formal, multi-record): G2 RKHS package -> point evaluation ->
    W_zero definition + Weil-witness construction attempt (G1 formal).
M3 (campaign): re-parameterize the 51-brick radial chain to W_zero and
    re-open P1 with hcolumn as an ASSUMED structural premise whose
    consistency is now the open capacity question.
Sequencing recommendation: M1 before touching Lean at all — if the index
cancellation fails numerically, C4 dies cheaply too.
```

RH is not claimed.
