# 1678 — The annular bound is the meet's local trace: kernel-diagonal reduction and the estimate program

Date: 2026-09-19.

Status: analysis record (hand-derived from committed definitions; no rig, no
Lean).  It prices the single remaining front-A object exactly, calibrates it
on the m = 1 model, and files the two candidate mechanisms.  The uniform
annular trace upper bound and RH remain OPEN; nothing here is claimed.

## 1. The exact reduction

Committed objects (pinning of record 1675): space `finiteSCarrier` = L²(R, du);
C = convolution by the compact involution test g* (support radius R);
P_n = M_{1_{[-n,n]}}; J the isometric source inclusion; carrier
= range of the meet R_0 = E ∧ Q with E = M_{1_{[log λ, ∞)}}, Q = H⁻¹EH;
the consumer basis is an ONB of the carrier itself (the consumers added in
1669–1676 all quantify over `HilbertBasis ι ℂ (sourceSoninCarrier lambda)`).

Because every basis vector satisfies R_0 e_i = e_i, the annular trace is

```text
tr Gram(N,n)  =  Σ_i || (P_n − P_N) C J e_i ||²
              =  || (P_n − P_N) C R_0 ||²_HS          (HS = Hilbert–Schmidt)
              =  tr( 1_annulus C R_0 C† 1_annulus ),
      annulus = { N ≤ |u| ≤ n }.
```

W†W has kernel A_{N,n}(u−v) := ∫ 1_annulus(x) g*(x−u) g(x−v) dx — the
annulus-restricted autocorrelation of g*, supported in |u−v| ≤ 2R.  Hence

```text
tr Gram(N,n)  =  ∫∫ A_{N,n}(u−v) R_0(v,u) dv du,
```

where R_0(v,u) is the meet's (a priori distributional) kernel.  Reading: the
annular trace sees the meet ONLY through its matrix elements at distances
≤ 2R — it is the LOCAL TRACE functional of the meet at scale 2R, evaluated
on annuli:

```text
Λ(χ) := tr( χ C R_0 C† χ )        for window functions χ ≥ 0,
front-A object:  sup{ Λ(1_{N≤|u|≤n}) : n ≥ N }  <  ∞.
```

This is the same functional family as the StripDensity content
(1581–1585 Thin(Λ), 1625/1630 trace layer) read at annulus geometry — the
double consumer is now explicit, and the 1677 adapted-compression brick is
the formal positivity bookkeeping that any comparison of two such local
traces may use (carrier bases are adapted bases).

## 2. Calibration: the m = 1 model (hand-derived)

For m ≡ 1, H = reflection, R_0 = M_{1_{[-a,a]}}, a = log(1/λ).  Then

```text
B_model(N)  =  ∫_{|u| ≥ N} ( |g|² ∗ 1_{[-a,a]} )(u) du,
      (|g|² ∗ 1_{[-a,a]})(u) = ∫ |g(u−v)|² 1_{[-a,a]}(v) dv.
```

Three exact features, each a calibration target any real estimate must
degenerate to:

```text
(i)   B_model(N) = 0 EXACTLY for N ≥ a + R   (support algebra; hard edge).
(ii)  the edge is CONTINUOUS: B_model(N) → 0 like the |g|² tail mass as
      N ↑ a + R (g is a C^∞_c test, so the approach is super-exponential).
(iii) for N < a the ramp is ~ ‖g‖² · 2(a−N) (interior, linear in the
      window deficit) — the fixed part, already trace-class per annulus
      (1672) and not the obstruction.
```

## 3. Why the meet is essential (kernel form of the 1599 lesson)

Replacing R_0 by E or by Q (one-sided bounds) makes the local trace

```text
∫_annulus ( |g|² ∗ 1_{[log λ, ∞)} )(u) du   ~   ‖g‖² · |annulus ∩ [log λ, ∞)|
```

which grows LINEARLY in n — infinite-rank (1599/1675).  The uniform bound is
therefore not a statement about C or about windows; it is a statement about
the meet's local trace.  No estimate that factors through a one-sided leg
can close it.  (F61 adds: this cannot be probed numerically either — the
meet reads as the forced subspace on any grid.)

## 4. The two mechanisms, priced

```text
(b1) CANCELLATION via the one-sided vanishing (1634):  e ∈ carrier means
     (K ∗ e)(−·) vanishes on a half-line.  The annular mass of C e for
     |u| ≥ a + R is then governed by what that vanishing forces on e's own
     tail — a backwards-uniqueness / uniqueness-continuation flavor.
     This is the mechanism consistent with the tower (the carrier is
     infinite-type, 1627).
(b2) KERNEL DECAY of R_0:  if the meet's kernel had off-diagonal decay at
     scale 2R, the double integral would be finite by pure integration.
     NOT currently available — no committed kernel for R_0 exists (1589:
     a locally-integrable reproducing-kernel diagonal is a sufficient
     condition, unproved here), and F61 forbids reading the kernel
     numerically.
```

The estimate program: prove (b1) directly, or land a kernel for R_0 first
(the 1625 basis-to-measure trace identity brick is the formal skeleton of
that route) and then run (b2).  Either way the target to degenerate to is
section 2's three features.

## 5. Next formal bricks identified (not yet built)

```text
(i)   monotonicity/sup characterization: tr Gram(N,n) is nondecreasing in n
      (orthogonal annular increments), so B(N) := lim_n tr Gram(N,n) is the
      canonical bound and the Pi statement reduces to one number per N.
      Needs the nesting product formula for kernelIntervalProjection
      (W ∘ W† across intervals) — medium MeasureTheory cost.
(ii)  the trace = kernel-energy identity for the annular window pair
      (ContinuousKernelHilbertSchmidt interface instantiated at C J R_0)
      once R_0 has a kernel — the (b2) formal skeleton.
```

## 6. Boundary

Front A's single open object is now exactly: the local trace functional of
the meet is uniformly bounded on annuli beyond the model edge.  Everything
formal around it (positivity 1674, trace-form consumers 1676, compression
bookkeeping 1677) is committed.  The estimate itself is the analytic core
of RH in this lane.  RH NOT claimed.
