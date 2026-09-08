# Record 1221 - E2a: correlation envelope generator (skeleton preregistration)

Pre-registration, committed BEFORE any generator run of this brick
(law 42).  Status: DORMANT / SUSPENDED (2026-09-08).  Record 1222 invalidated
the 1220 implementation, and record 1223 suspends its parent 1219 until a
healthy-`CompactLog`, B5-shaped consumer is named.  No parameter addendum,
generator run, or Lean consumer may be started from the present skeleton.
Parents: 1219 (brick E2), 1220 (numeric-layer probe, GO gate, falsifiers F1/F2).
Prospective consumers: 1219 bricks E3a/E4/E5 and the landed record-1218 chain
(`q28_absolute_1218_of_sameParity`).  No P2, no SourceRH, no RH.

## 1. Target

Emit, per the record-1219 E2 brick, Lean-certified exact rational
envelope data for the two-window correlation

```text
C_ij(x) := (pairTest (classTestFamily 2 htwo) i j).test x
         = integral t in (-2, 2), W_i(-t) * W_j(x - t),
```

in the three readout shapes E2 names:

```text
(a) x = 0: NOT re-generated.  C_ij(0) = classGramEntry 2 i j is already
    owned by the landed q28 base-moment certificate chain
    (q28_baseMoment_bounds_of_concrete_certificate, 1131/1145 modules,
    axiom-clean).  E2a consumes it; nothing here re-proves it.
(b) x = log n at the 24 visible prime powers n <= 53: point rational
    intervals (the E4 log-readout intervals are inputs, not outputs).
(c) uniform rational interval bounds for C_ij on every quadrature cell
    of the pinned y-partition of (0, 4): the direct input of E3a.
```

## 2. Machinery (the record-1220 pipeline, verbatim semantics)

The generator ports the 1220 probe machinery 1:1; no numeric decision
is re-derived on the Lean side:

```text
- s-partition of [0, S_MAX] with in-cell Taylor models of
  g(s) = -1/(1-s^2), bump bounds via exact exp partial sums
  (1137-style), tail budget beyond S_MAX;
- substitution s = t/2, u = y/2 - s with per-leaf u-range clamping;
- y-partition of (0, 4) pre-split at Y_MAL: Maclaurin kernel-moment
  branch on y1 <= Y_MAL, geometric branch on y0 > 0 (the run2 crash
  fix, commit b5b4bfa - the invariant "no cell straddles Y_MAL" is
  part of the pinned semantics);
- the bracket cancellation 2 e^{y/2} P_j(u) b(u) - 2 P_i(-s) b(s) is
  enclosed INSIDE the s-integral, never through C(y) and C(0)
  separately;
- per-leaf u-Taylor truncation budget of order nu with the honest
  remainder; PAIR_SKIP / REM_TARGET / GRID floors exactly as pinned.
```

Registered review note (inherited, adjudicated by falsifier F2): in the
1220 entry-assembly leaf loop the loop variable `sign` is syntactically
dead in the body, so the region sum enters totalH twice.  The intended
semantics (evenness factor-2 vs a missing s < 0 half) is decided
EMPIRICALLY by the 1220 box-containment check at the 2.4e-13 budget -
a wrong factor shows up as an O(component) displacement, far above the
budget.  E2a inherits the 1220 verdict verbatim; this prereg does not
pre-judge it.

## 3. Emitted artifacts (1218 F5 pattern)

```text
Generator:  docs/proofs/1221_generate_e2a.py
Modules:    ConnesWeilRH/Dev/C1GateEntryEnvelopeQ28.lean (+Audit)
```

The generator reads the pinned parameter block and the official probe
round's ledger; it asserts EVERY norm_num identity it will emit over
exact Fractions BEFORE emission (mismatch = exit 1, no module emitted -
the 1218 F5 pattern).  Emitted lemmas: per probed entry, the cell /
tail / readout rational data plus the consuming interval lemmas, in the
1218 generated-module house style.

## 4. Parameter sockets (pinned by the 1220 GO addendum, NOT here)

```text
S_MAX, d_S (s-model degree), N_S (s-cells), Y_MAL, N_Y (y-cells),
nu (u-Taylor order), PAIR_SKIP, REM_TARGET, GRID, per-constant series
lengths (pi, log 2, gamma, e^-4 chains), E4 log-readout width (1e-45).
```

## 5. Registered branches

```text
GO     1220 verdict: total entry width <= 5e-13 AND (0,0)/(7,7)
       inside the committed MLo_q28M/MHi_q28M boxes.
       -> 1220 addendum pins sec. 4 (commit BEFORE the generator run)
       -> generator run -> E2a build per sec. 6.
NO-GO  this prereg stays DORMANT: no generator run, no Lean build.
       The only legal recoveries are the registered 1219/1217
       amendment paths (never hand-widening, 1097).
```

## 6. Acceptance

```text
A1  generator run emits with zero falsifier aborts; the emitted
    per-entry widths reproduce the official probe round's realized
    widths entry-for-entry.
A2  E2a module builds green; every Audit headline prints exactly
    [propext, Classical.choice, Quot.sound]; 0 sorryAx, 0
    ofReduceBool, no new-module warnings.
A3  hygiene scan before push, upstream read-back after.
A4  per-cell and per-readout margins reported numerically in the
    verdict record.
```

## 7. Scope

q28 only (q38/q48 chains wait per the record-1218 scoping).  All 20
same-parity entries are in scope for the envelope; generator round 1
covers the two probed entries (0,0)/(7,7) - the entries the GO gate
actually certified - and the remaining 18 follow on the SAME pinned
parameters in later rounds, each with its own generation-time asserts.
RH NOT claimed.
