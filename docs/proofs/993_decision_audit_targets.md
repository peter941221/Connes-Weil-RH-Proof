# 993 — Decision-audit: which "route-changing" targets are already closed vs truly open

Date: 2026-08-11. Status: repo-audit / decision-confluence (no new Lean). RH NOT claimed.
Prompt: head to the route-changing lane (infinite-carrier Gate `(*)`, A0/C2, Burnol).

## Result (surprising but clean)

Two targets the route log flags as "open" have ALREADY been closed in-library:

1. **A0 / Route-C nonzero carrier (docs/826 / 827 C2-C3) — CLOSED.**
   `ConnesWeilRH/Dev/C3NonzeroCarrierThrough.lean` proves, axiom-free (`sorry`) :
   - `stepCarrierLp_crossing_inner_pos (b) (hb:0<b) : 0 < Re <stepCarrierLp b,
        cc20SingleCrossingOperator b (stepCarrierLp b)>`  (the A0 scalar = b > 0)
   - `stepCarrier_traceAlong_eq_b` / `stepCarrier_traceAlong_re_pos` : the
     Hilbert-basis diagonal trace = `b > 0` on EVERY basis.
   So docs/827's A0 "does a positive carrier exist" is answered YES with a concrete
   step carrier.  There is no remaining C2/C3 gap to build.

(b) The Gate-3U proof-717 formal dichotomy obligation — ALREADY STATED.
   ConnesWeilRH/Dev/Gate3UDichotomyProbe.lean declares
   `gate3UDichotomyObligation lambda := all family, leakage=0 -> visiblePrimes=[]`
   (the docs/872b §5 "make the open a Prop obligation" step is present).

## The one genuinely-open lane (cannot be closed by assembly)

The infinite-carrier Gate front reduces to ONE analytic identity on the
J-orthogonal component (docs/872/872b):

    (*)  (I - P) F = -(I - P) D   on (range P)^\perp,

equivalently the forward band coframe `F = P_band o (normalizedInverse) o J`
equals `-(D - J)` off the Sonin band.  Facts that pin it:
  - `J^dag F = 0`, `J^dag D = I`, `P F = 0`, `P D = J`, `P (D-J) = 0` all proven;
  - the P-component of `F-(D-J)` is automatically 0; the whole content is `(*)`;
  - numerics (824/884): `(I-P)D` outer channel ~0.61, scale-robust, never decays;
  - deciding term `F` on `(range P)^\perp` needs the exact Sonin intersection
    `R0`, numerically unreachable (812/818/819).
So `(*)` is exactly ONE new analytic identity on the off-Sonin channel, and it
requires either a genuinely new (projected spectral) analysis or a concrete
in-library nonempty carrier that provably violates it (a formal route refutation).

## Honest route read

- There is NO small, buildable, route-deciding lean gap left that isn't `(*)`.
  All "concrete carrier / nonzero trace / dichotomy" items are closed or stated.
- `(*)` and Burnol are the only true new-analyze bottoms; both are not assembly
  leaves and require either a new operator identity or a proven refutation.
- I will NOT claim a closure I did not build. The correct next investment is a
  focused analysis of the exact Sonin-intersection `R0` structure for `(*)`, or
  accepting `(*)` as the single hard bottom and re-scoping canonical Gate-3U to
  the (already-closed) finite-band route-A.

RH not claimed. No axiom/sorry introduced.
