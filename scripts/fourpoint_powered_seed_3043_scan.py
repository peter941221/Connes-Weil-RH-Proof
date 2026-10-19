#!/usr/bin/env python3
"""Record 3043: bounded powered-seed same-owner determinant scan.

This is a model-grade sign screen only.  It does not certify the owner,
quadrature, the universal rho quantifier, or any tail bound.
"""
from __future__ import annotations

import json, math, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_actual_owner_1980 as owner_probe
import fourpoint_owner_density_1959 as legacy

SEED_SCALE, SEED_POWER, N = 0.5, 10, 4
RHO_GRID = [(0.51, 10.0), (0.51, 14.1347251417), (0.55, 14.1347251417),
            (0.60, 20.0), (0.70, 30.0)]
SIGMA_GRID = (0.0, 0.5, 1.0)
LAMBDA_FIXED = 24.0

def make_seed(order=220):
    nodes, weights = np.polynomial.legendre.leggauss(order)
    x, w = 2.0 * nodes, 2.0 * weights * owner_probe.smooth_seed_raw(2.0 * nodes)
    def transform(s):
        a = np.asarray(s, dtype=complex).reshape(-1)
        out = np.empty_like(a)
        for i in range(0, len(a), 500):
            z = a[i:i+500]
            out[i:i+500] = np.sum(np.exp((SEED_SCALE*z)[:, None] * x[None, :]) * w[None, :], axis=1) ** SEED_POWER
        return out.reshape(np.asarray(s).shape)
    return transform

def one(rho, sigma, seed, xi):
    R = complex(*rho)
    owner, targets, _, known = owner_probe.build_owner(R, N)
    vals = [owner_probe.target_value(R, z) for z in owner]
    seed0 = complex(seed(np.array([0j]))[0])
    axis = sigma - 2j * math.pi * xi
    base = owner_probe.cardinal_transform(targets, [1+0j]*len(targets), seed0, axis, seed)
    corr = owner_probe.cardinal_transform(owner, vals, seed0, axis, seed)
    poly = np.real(legacy.P_from_nodes(xi, [z-0.5 for z in targets[:4]]))
    rows=[]
    for n in range(5):
        sr=2.0*(n+2)
        kernel=legacy.rig.sigma_vec(2.0*math.pi*xi)
        pp=legacy.rig.prime_powers_up_to(math.exp(sr))
        for integer, vm in pp:
            kernel += 2.0*vm/math.sqrt(integer)*np.cos(2.0*math.pi*xi*math.log(integer))
        dens=np.abs(base)**(2*(n+1))*np.abs(corr)**2
        C=float(np.trapezoid(kernel*dens,xi)); b=float(np.trapezoid(kernel*poly*dens,xi)); D=float(np.trapezoid(kernel*poly*poly*dens,xi))
        det=C*D-b*b
        rows.append({"n":n,"C":C,"b":b,"D":D,"det":det,"vertex_lambda":b/C if C else None,
                     "fixed24_q":C*LAMBDA_FIXED**2-2*b*LAMBDA_FIXED+D,
                     "vertex_signs":bool(C>0 and b>0 and det<0),
                     "fixed24_negative":bool(C*LAMBDA_FIXED**2-2*b*LAMBDA_FIXED+D<0)})
    return {"rho":list(rho),"sigma":sigma,"known_zero_count":len(known),"rows":rows}

def main():
    seed=make_seed(); xi=np.arange(-25.0,25.0001,0.05)
    scans=[one(r,s,seed,xi) for r in RHO_GRID for s in SIGMA_GRID]
    vertex=[x for q in scans for x in q["rows"] if x["vertex_signs"]]
    fixed=[x for q in scans for x in q["rows"] if x["fixed24_negative"]]
    report={"record":3043,"status":"MODEL_SCAN_ONLY","seed":{"scale":SEED_SCALE,"power":SEED_POWER},
            "rho_grid":RHO_GRID,"sigma_grid":SIGMA_GRID,"fixed_lambda":LAMBDA_FIXED,
            "counts":{"scan_points":len(scans),"vertex_sign_pass":len(vertex),"fixed24_negative":len(fixed)},
            "scans":scans,"nonclaims":["not a proof","known-zero owner under-approximation","sampled trapezoid","no universal rho conclusion"]}
    out=ROOT/"results"/"3043_powered_seed_sign_scan.json"; out.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))
if __name__=='__main__': main()
