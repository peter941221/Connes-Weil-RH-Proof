# Record 2729: full-line envelope re-audit

Task card: owner = exact stored row-B cardinal model from 2720.
Consumer = three row-B strip pins; target = correct cell distances and
cover both signs beyond 600 without changing the seed or constants.
Budget = one bounded source/model pass, <= 15 minutes, <= 1 GiB RAM,
no Lean build. Completion = same-run legacy control, corrected finite
scan, analytic infinite tail, and an explicit rung-degree verdict.
Stop on control failure or a failed pin; no automatic refinement.

Historical 2720/2727 artifacts remain unchanged. The new run is a model
audit, not a kernel-checked certificate or an RH result.


## Analytic tail derivation and reduced-rung obstruction

Write x = |t| >= T > max active |Im z|. For an active cardinal term,
m is the number of other owner nodes, p is the pin's frequency weight,
and k is a derivative rung. Set

```text
A_w(T) = sqrt((ds_w/T)^2 + (1 + |Im w|/T)^2)
b_z(T) = 1 - |Im z|/T > 0
B_z,k(T) = |c_z| prod_w A_w(T)
           * (Ez D_k 2^k / b_z(T)^k)^10 / (2*pi)^p
term_z(t) * (x/(2*pi))^p <= B_z,k(T) x^(m+p-10k)
```

This follows from the triangle inequality and |t-Im z| >= x-|Im z|,
so it covers both signs. If m+p-10k <= 0, its supremum beyond T is
bounded by B_z,k(T) T^(m+p-10k). Minimize over eligible rungs per term,
then sum. A positive exponent cannot certify an infinite supremum.

For row-B correction: m=55 and p=2. With rungs <=4 the exponent is
17; with rungs <=5 it is 7; k=6 gives -3. In fact the finite-rung
positive term envelope itself grows at that rate asymptotically:
the highest available rung eventually wins the min, and all active
coefficients are positive. This is a no-go for that envelope, NOT a
lower bound on the actual cardinal function (which may cancel).
Thus record 2727's finite-scan reduction to D_4 alone does not hold on
the full line. At least a rung >=6, or a different proved tail method,
is needed for this correction owner. No D_4-only campaign follows.

The run preserves the historical parent source and clones exactly one
expression for corrected finite scans. Its arithmetic and stored constants
remain model-grade; no claim of directed rounding is made. The parent's
D-table endpoint sliver uses a neighboring-cell value times a safety
factor and point scans; that endpoint proof remains an independent duty.


## Landed run and route decision

All eight controls passed, including three bitwise legacy reproductions,
crossing/endpoint/external distance tests, an exact monomial tail example,
and rejection of a positive tail degree. Exit code 0. Historical 2720
source and artifacts are unchanged. Corrected finite scans preserve the
reported maxima; crossing-cell repair does not move these maxima.

```text
quantity        corrected finite       tail >=600, full table    pin
C4              6.0524298631e7          8.4746013881e-61           6.1e7
C2              2.8161344216e7          6.2561287516e-8            2.9e7
q               2.5248153557e-16        1.0191397754e-68           2.6e-16
```

Full-table conditional model bounds clear all three pins. The selected
infinite-tail rung is 7 for every active term, including correction
exponent -13. This supports a possible split proof: rungs {1,2,3,4} for
|t|<=600 and rung 7 for the exterior. It does not require formalizing
orders 5,6,8..12 if this split is certified. The prior D_4-only plan is
closed at global grade; Route B itself is not disproved or re-frozen.

Next proof obligations: certify D_4 and a suitable high rung (7 is the
landed conditional choice), their endpoint regions, stored constants and
arithmetic, finite-cell coverage, and the split-tail inequalities. Then
re-seed the actual carrier and address the genuine-rho interpolation and
gate premises. Exact mass 3 remains proved. No Lean build was needed or
performed in this audit; no universal producer premise was removed.

Evidence: `scripts/full_line_envelope_reaudit_2729.py` and
`results/2729_full_line_envelope_reaudit.json`. A null C2 global value in
the cut-4 row means no finite bound from that envelope, never zero.
