# 2341 - Single-sided chord enclosure for the repaired strip norms

Date: 2026-10-01.

Status: ONE-SIDED-PANEL-TRANSFER-CONDITIONAL-ON-NODE-UPPERS.

单边上界（one-sided upper bound）只保证积分不会超过给定费用，不保证上下误差
都小；弦线（chord）是在相邻两个节点之间连的直线，用它代替曲线做积分。
节点上界（node upper bound）要求每个采样点的数字不小于真实模长，类似每一件
货物先称够重量再相加。模长（complex modulus）是复数在平面上的长度，不能用
实部的绝对值替代。曲率（curvature）在这里指二阶导数对直线近似误差的控制。

The replacement passes 101/101 sigma nodes under the unchanged pin
2644542.8515. The maximum is at j=-50, approximately 706456.2163439568,
compared with the corrected 2340 reading 706456.1761485816. This is not
an independently certified node sum, a Lean transfer theorem, a live-owner
handoff, a signed-kernel charge, or an RH result.

## Object and the actual inequality needed

The stored source is a sum of radius-R smooth bumps with complex
coefficients and modulation exp(i theta x). The baseline R values are the
stored binary64 results width*width, not their exact real squares. The
ideal coefficients and exact-radius changes remain charged by 2339/2340.
No owner change or P-only multiplier is introduced.

F is either stored base or stored correction. F^(k) denotes its kth
derivative; k=0 is the function and k=2 its second derivative. For a fixed
real sigma define the complex-valued function

  V(x) = exp(sigma x) F^(k)(x).

Its modulus |V| is the integrand in the strip norm. The trapezoid T joins
endpoint values with a straight line and integrates that line. The consumer
needs only integral |V| <= T + allowance; it does not need |integral-T|.

The former wording that a zero-free complex function has
|(|V|)''| <= |V''| is false. For V(x)=x+i epsilon with epsilon>0,
V''=0 but (|V|)'' at zero is 1/epsilon. Absence of zeros does not remove
the extra transverse-motion term. This does not refute the single-sided
panel upper used here: |V| is convex in that example and T is an upper.

## Cell proof, including complex phases and zeros

Let a<b be a cell, h=b-a, and assume |V''(x)|<=M on the cell. Let x be
any point of the cell. If V(x) is nonzero choose a complex unit direction e
such that Re(conjugate(e) V(x))=|V(x)|. If V(x)=0 the final inequality
holds immediately. For the nonzero case put

  f(t) = Re(conjugate(e) V(t)).

Then f'' >= -M because the modulus of a real projection is no larger than
the complex modulus. Thus f(t)+(M/2)t^2 is convex: its value lies below
the straight line through the endpoints. Subtracting the quadratic gives

  |V(x)| <= ((b-x)/h)|V(a)| + ((x-a)/h)|V(b)|
            + (M/2)(x-a)(b-x).

Integrating the quadratic error over one cell gives M h^3/12. Summing
uniform cells across an interval of length 2R gives

  integral |V| <= T_h(|V|) + (h^2/12)(2R) M.

This proof does not differentiate |V| and does not require zero exclusion.
The endpoint flatness of the bump is sufficient for V to be C^2 across
its support edge. A zero-count certificate is retained as a historical
baseline provenance gate, not used in the replacement analytic inequality.
No lower integral bound or absolute quadrature-error statement is asserted.

## Directed majorants and coordinate charge

The ladder m_j bounds |F^(j)| by summing complex coefficient moduli and
the bump derivative bounds with every theta term retained. Product
differentiation yields the curvature majorant

  M = exp(|sigma| R) (m_(k+2) + 2 |sigma| m_(k+1) + sigma^2 m_k).

The script evaluates this expression and h=2R/(240001-1) in Arb arithmetic.
It adds only max(0, directed_panel - stored_panel) to the 2340 upper. A
smaller replacement panel does not reclaim any prior allowance.

The derivative constants are checked independently from
phi(u)=exp(-30/(1-u^2)). Its jth derivative has the form
exp(-30/q) P_j(u)/q^(2j), q=1-u^2. The polynomial recurrence is

  P_(j+1) = q^2 P_j' + (4j u q - 60u) P_j.

For 0<q<=1 and j<=4, q^(-2j) exp(-30/q) <= exp(-30), since
the logarithmic derivative is (30-2j q)/q^2 >= 0. The polynomial
coefficient absolute sums for j=0..4 are 1, 60, 3720, 236160, 15130080;
the registered constants 1, 60, 3900, 245160, 23402880 dominate them.

The historical numpy linspace coordinates are binary64 numbers, not
mathematically uniform nodes. Let delta be the maximum exact rational
difference between the reconstructed linspace coordinates and
-R+2R i/(N-1). The modulus integrand has Lipschitz bound

  L = exp(|sigma| R) (m_(k+1) + |sigma| m_k).

Lipschitz means a displacement d changes its value by at most L d.
The quadrature weights sum to 2R, so 2R delta L is an upper charge for
replacing stored coordinates by exact uniform nodes. This charge is
added before the already registered exact-sigma weight transfer. The
identity of the reconstructed coordinates with the original run remains
an explicit open premise; the old artifact contains no coordinate array.

## Remaining source-level obligation

Each of the 101 baseline point rows is checked against its sigma JSON,
and all files and the three helper sources receive SHA256 bindings. Those
checks identify the stored data, but do not prove the values are uppers of
the exact weighted nodal sum.

In particular, 2303 calls the 2234 node evaluator with round-to-nearest
MPFR arithmetic, then adds a magnitude-based slack and binary64 ulps.
The sigma accumulator also uses round-to-nearest (MPFR rounding code 0),
with an outward factor and output inflation. This is not automatically a
directed interval chain just because the computation uses MPFR. The slack
and accumulation guarantees must be derived or independently enclosed;
an unchanged status string and three nextafter operations are not that proof.

The new artifact therefore retains point_node_upper_theorem_proved=false,
coordinate_grid_identity_with_original_run_proved=false, and
transfer_theorem_imported_in_lean=false. The next gate is the exact
nodal-upper bridge, not another refinement of the panel number.

## Validation and evidence

- scripts/routea_one_sided_panel_transfer_2341.py.
- scripts/routea_one_sided_panel_selftest_2341.py.
- results/2341_one_sided_panel_transfer.json.
- results/2341_one_sided_panel_validation.json.
- scripts/routea_corrected_strip_envelope_2303.py, chunk_worker and sigma_worker.
- scripts/routea_weighted_zero_direct_product_outward_2234.py, node_bounds.

Controls cover the sharp concave quadratic, a zero-crossing affine
function, a nonzero complex affine function with arbitrarily large
modulus curvature, quadratic refinement scaling, both signs of sigma,
exact dyadic grids, derivative-polynomial constants, malformed provenance,
helper source hashes, and retained no-handoff flags.

WSL resource-runner validation: 11/11 new selftests and 12/12 predecessor
2339 selftests pass. A second full 2341 run reproduces the artifact byte
for byte. The maximum reconstructed coordinate gap is exactly
4757/2814749767106560000. The maximum product increases by approximately
0.0401953752 after the directed-panel top-ups and coordinate charge.

## Next steps

1. Certify the weighted nodal uppers or prove the current magnitude slack
   and accumulation allowance. Completion requires a per-channel inequality,
   not only a comparison with the ordinary float evaluator.

2. Bind the spatial coordinate arrays to their actual construction inputs
   and verify the coordinate displacement charge against the stored run.
   Completion requires matching node identities, not matching node counts.

3. Only then formalize the same-owner triangle transfer and connect it to
   the strip consumer. The composed support and signed prime-kernel budget
   remain separate obligations; no 2R prime-book shortcut is licensed.
