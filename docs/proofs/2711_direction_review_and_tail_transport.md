# Record 2711: direction review and weighted tail transport

Status: GEOMETRIC TRANSPORT IMPLEMENTED; COMPLETE-OWNER INPUTS STILL OPEN.

## Direction review

The 2710 estimate is compatible with the final FourthOrderSpectralTail domain:
both signs of frequency, full complex norm, real parts in [0,1], height at
least 1 and at least twice the source height. The extra strip premise on rho
must be supplied for a genuine source zero. The improvement changes only the
estimate, not the function, lambda, support, prime domain or signed gate.
It is therefore worth retaining as a local ingredient, not as a producer.

The direction is NOT to certify the three proxy rows and extrapolate RH.
`fourpoint_actual_owner_1980.py:104` enumerates known zeros via mpmath with a
maximum index, and `:155` constructs an explicitly under-approximate owner.
`fourpoint_gate_tail_pairing_2033.py:119` uses a synthetic point with real
part 0.55. Its C4/C2 are sampled maxima, not global upper enclosures.
Those inputs cannot identify a complete formal owner or a genuine source zero.

Record 2128 further shows why adding nodes is not a harmless completeness fix:
the fixed-n full-product stress changes the gate signs and dramatically grows
the correction. Its scope is n=6, not a theorem against all n or the new n=3
proxy rows. It nevertheless forbids assuming owner enlargement is cost-free.
Record 1799 W4 already records near-line node collision; no novelty is claimed.
Parameters may depend on rho; a global uniform bound is not required, but
their dependence cannot be silently discarded.

## New precise transport statement

`weighted_transformed_square_le` in `C1HighShellGeometry2710.lean` applies to
any complex transform f and to the EXACT four-point polynomial P. It bounds
the weighted norm of

```text
[(P(z)-lambda)*f(z)] * conjugate([(P(1-conjugate(z))-lambda)*f(1-conjugate(z))])
```

using the raw-square input

```text
abs(Im z)^12 * (norm(f(z))*norm(f(1-conjugate(z)))) <= R.
```

Its conclusion has constant `d*(d+abs(lambda))^2*R`, with d=169/16.
Thus the geometric factor is fully checked on the transformed reflected
product, rather than only on four independent distances. The raw bound R is
an explicit analytic premise. No target positivity conclusion is stored in it.

To specialize to the existing owner, the remaining rewrites are the centered
selected-owner square identity and `laplaceAt_fullOrbitSpanVector`, with f
the uncentered raw transform. Existing raw twelfth-order decay suggests
`R=(2*pi)^12*(q^n*C4*C2)^2`. This source-level identification has not been
compiled as an end-to-end project tail theorem; no project aggregate was built.

## Stop/go result

```text
retain new geometric method                     YES
transport through exact reflected product        implemented and audited separately
certified complete-owner C4/C2/q/prefix/gate       NOT SUPPLIED
reopen frozen family / scale entry campaign       NO
```

The next research contract must produce a parameter-dependent analytic bound
for the exact full interpolation owner and compare it with the same-owner gate
at the same n and lambda. A mere finite constant-existence theorem is not a
quantitative closure. Until that bound is supplied, no expanded n scan, higher
degree run, new entry tree or aggregate build is justified.

Budget for this step: one small module, one worker, 120 seconds per check;
source review only for analytic readiness, no fresh numerical evaluation.
The successful run log is retained separately as
`results/2711_weighted_tail_geometry_lean.log`.

Final validation: Lean exit status 0, 46.68 seconds wall time, peak resident
memory 2,692,404 KiB, OLean 687,880 bytes. All five audited declarations
(the four 2710 leaves and the new transport theorem) have exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. Checked source
SHA-256: `6d3b63fc40ff76906f368783ab8cbd79435e35a028ac43a58a6cc9370e8ecae0`.
The initial run failed because the new polynomial definition needed the
`noncomputable` annotation; the final log records the successful corrected run.
