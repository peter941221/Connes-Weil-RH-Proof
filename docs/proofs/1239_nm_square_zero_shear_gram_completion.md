# 1239 - G7 square-zero shear Gram completion

Date: 2026-09-09.

Status: `KILLED`; paper candidate only.  No Lean declaration,
numerical run, positivity theorem, or RH claim is opened.  Consumer: the
healthy-`CompactLog`, selected-detector, same-owner B5 gate from map record
[`003`](../map/003_b1_b5_minimal_exit_route_selection.md).

## 1. Candidate formula

The existing finite-visible-prime geometry supplies a square-zero oblique
shear

```text
N_S = Q_S - R,
R N_S = N_S,   N_S R = 0,   N_S^2 = 0,
```

with `R` the source Sonin projection and `Q_S` the pulled finite-S target
projection.  These identities are formal in the earlier structural leaves
(`CCM24FiniteSGatePhysicalObliqueShearReduction`); they are used here only as
an algebraic seed, not as a Gate-3U consumer.

For the selected detector write `W_g` for its positive whole-line detector
operator.  The proposed internal kernel is the Gram completion

```text
G_{g,S} := (I + N_S)^* W_g (I + N_S).
```

It is positive by construction and expands exactly as

```text
G_{g,S}
  = W_g + W_g N_S + N_S^* W_g + N_S^* W_g N_S.
```

The middle two terms are the signed shear response; the last term is the
internal leakage square.  This is the first candidate that keeps the
correction inside one positive kernel while retaining the genuinely
non-separable finite-S channel.

## 2. Translation obligations

G7 is admissible only if one same-owner theorem supplies all of the following:

1. the old `N_S` is transported to the active `CompactLog` carrier and uses
   the selected detector's actual visible-prime list;
2. the finite-cutoff version of `G_{g,S}` is trace-class and positive before
   the trace is taken;
3. the cross term has the exact active response orientation (no illegal trace
   cycle or adjoint swap);
4. the baseline `W_g` term and leakage-square term combine with the literal
   archimedean/visible-prime ledger, rather than being subtracted externally;
5. the resulting positive trace converges to the same-owner `qw(g)`.

The square-zero identities alone do not discharge item 4: nilpotence removes
only consecutive `N_S` products, not the detector-crossed term.  The old
structural record explicitly exhibits this obstruction in a two-dimensional
model.  Thus G7 is not a relabeling of the rejected `M = I-K` correction.

## 3. Owner-level symbolic screen

The active owner is the source Sonin carrier, with inclusion `J` and source
projection `R = J J^*`.  The existing formal identities give

```text
N_S R = 0,   R J = J,
```

and therefore, before any trace is taken,

```text
N_S J = N_S R J = 0,
(I + N_S) J = J.
```

Consequently the only same-owner compression of the proposed Gram kernel is

```text
J^* (I + N_S)^* W_g (I + N_S) J = J^* W_g J.
```

The two shear cross terms and the leakage square disappear identically.  An
uncompressed ambient trace would retain them, but it would no longer be the
selected-detector trace on the healthy source owner and would violate the
same-owner contract.  Thus G7 cannot carry the finite-S response it was
invented to retain.

This is a symbolic owner-level no-go, backed by the formal square-zero and
source-range identities in `CCM24FiniteSGatePhysicalObliqueShearReduction`;
it does not depend on a numerical experiment or on a cyclic trace move.

## 4. Cheap falsifier and decision rule

Kill G7 immediately if the exact expansion forces either of these shapes:

```text
positive trace - baseline trace - leakage trace -> qw,
```

or a response orientation that can be repaired only by an unproved cyclic
trace move.  Conversely, a surviving formula must identify the baseline and
leakage terms as actual same-owner Weil channels inside the positive kernel;
their separate limits may not be assumed.

The screen failed at the owner-compression identity, so no Lean
Gram-completion brick or numerical prototype is authorized.  Any replacement
must act on a different, explicitly justified owner and then re-prove the
same-owner `qw` readback; merely moving the trace to the ambient carrier is
not a repair.

RH is not claimed.
