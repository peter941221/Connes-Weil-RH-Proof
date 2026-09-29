#!/usr/bin/env python3
"""Recon for 2253: measure per-node charge split of the direct-product
screen on the committed 2197/2234 construction grid."""
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_direct_product_outward_2234 as o34  # noqa: E402
import routea_weighted_zero_direct_product_mass_screen_2197 as s97  # noqa: E402
import routea_opposite_gates_height_1994 as r94  # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402

import mpmath as mp  # noqa: E402

fam, base, corr, a_max = o34.build_construction()
print("nodes", len(fam), "a_max", a_max)

# rebuild node labels exactly like 2249.build()
rho = (0.5 + s97.DELTA) + 1j * s97.GAMMA
nodes, values = r94.owner_nodes_ext(rho, s97.GAMMA)
radius = r80.ball_radius(rho, 0)
mp.mp.dps = 50
for index in range(1, 31):
    height = float(mp.im(mp.zetazero(index)))
    z = 0.5 + 1j * height
    if abs(z - rho) <= radius and all(abs(z - e) > 1e-6 for e in nodes):
        nodes.append(z)
        values.append(0j)
print("nodes", len(nodes), "radius", radius)

labels = []
for z, v in zip(nodes, values):
    if v != 0:
        kind = "target"
    elif abs(z.imag) <= 1e-9:
        kind = "real_pin"
    elif abs(z.real - 0.5) > 1e-9:
        kind = "offline_pin"
    else:
        zval = float(abs(mp.siegelz(mp.mpf(z.imag))))
        kind = "zero" if zval < 1e-9 else "kills_pin"
    labels.append(kind)
print("labels", labels)

NX = s97.NX
x = np.linspace(-a_max, a_max, NX)
dx = (2.0 * a_max) / (NX - 1)
tw = np.full(NX, 2.0)
tw[0] = tw[-1] = 1.0
wgt = dx / 2.0 * tw
ex = np.exp(1.0 * x)

K = s97.K
qj = np.zeros(len(fam))
pj = np.zeros(len(fam))
for j, (a, th) in enumerate(fam):
    u = x / a
    q = 1.0 - u * u
    mask = q > 0.0
    phi = np.zeros(NX)
    phi[mask] = np.exp(-K / q[mask])
    e1 = np.zeros(NX)
    e2 = np.zeros(NX)
    e1[mask] = -2.0 * K * u[mask] / (a * q[mask] ** 2)
    e2[mask] = (-2.0 * K / (a * a)
                * (1.0 / q[mask] ** 2 + 4.0 * u[mask] ** 2 / q[mask] ** 3))
    g = e2 + e1 * e1 - th * th
    h = 2.0 * th * e1
    d2 = np.hypot(g, h) * phi
    qj[j] = abs(base[j]) * float(np.sum(wgt * ex * d2))
    pj[j] = abs(corr[j]) * float(np.sum(wgt * ex * phi))

print("sum q_j =", qj.sum(), " artifact base_D2 = 7945.304436068302")
print("sum p_j =", pj.sum(), " artifact corr_M0 = 1196.4645507389077")
print("base_abs_max", np.abs(base).max(), "corr_abs_max", np.abs(corr).max())

B_upper = 9506275.102584327
mult = 128.70692502980964
P = 1196.4645507389077
db = 7945.304436068302
tp2 = (2.0 * math.pi) ** 2
tail = 4894093747.764274
budget = tail / 62.0
budget_mass = B_upper / 62.0
print("budget ledger units", budget, "budget mass", budget_mass)

order = sorted(range(len(fam)), key=lambda j: -qj[j])
print("\n j  label        a     th        |beta_j|      q_j        T_j        q_j/budM  T_j/bud")
for j in order[:12]:
    Tj = 4.0 * mult * qj[j] * P
    print("%2d %-10s %6.3f %9.4f %12.4e %12.4e %12.4e %10.4f %10.4f" % (
        j, labels[j], fam[j][0], fam[j][1], abs(base[j]), qj[j], Tj,
        qj[j] / 128.15, Tj / budget))
print("max qj over zeros:", max(qj[j] for j in range(len(fam)) if labels[j] == "zero"))
print("max Tj:", 4.0 * mult * qj.max() * P, "over node", int(np.argmax(qj)))
