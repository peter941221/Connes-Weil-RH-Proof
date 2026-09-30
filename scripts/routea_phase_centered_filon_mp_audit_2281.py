"""2281: high-precision audit of the phase-centred Filon screen.

This does not certify the tail. It recomputes selected transforms with 100-digit
arithmetic from the same stored owner data and compares them with binary64.
"""
import argparse
import json
import math
from pathlib import Path
import sys
import mpmath as mp
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import routea_phase_centered_filon_tail_screen_2280 as f2280
CAPTURE=ROOT/'results/2275_gap_owner_audit.json'
OUT=ROOT/'results/2281_phase_centered_filon_mp_audit.json'


def mp_complex(value):
    return mp.mpc(mp.mpf(repr(float(value.real))),mp.mpf(repr(float(value.imag))))

def mp_owner(y,families,coefficients):
    total=mp.mpc(0)
    for coefficient,(width,theta) in zip(coefficients,families):
        radius=mp.mpf(repr(width))**2
        q=1-(y/radius)**2
        if q>0:
            phi=mp.exp(-30/q)
            total += mp_complex(coefficient)*phi*mp.exp((mp.mpf('0.5')+1j*mp.mpf(repr(theta)))*y)
    return total

def cheb_coefficients(values):
    n=len(values)-1
    coeff=[]
    for k in range(n+1):
        total=mp.mpf('0')
        for j,value in enumerate(values):
            weight=mp.mpf('0.5') if j in (0,n) else mp.mpf(1)
            total += weight*value*mp.cos(mp.pi*k*j/n)
        coeff.append((2*total/n) if k else total/n)
    return coeff

def cheb_to_power(coeff):
    powers=[[mp.mpf(1)], [mp.mpf(0),mp.mpf(1)]]
    for k in range(2,len(coeff)):
        previous=powers[-1]
        before=powers[-2]
        doubled=[mp.mpf(0)]*(len(previous)+1)
        for i,value in enumerate(previous): doubled[i+1]+=2*value
        for i,value in enumerate(before): doubled[i]-=value
        powers.append(doubled)
    result=[mp.mpc(0)]*len(coeff)
    for scalar,poly in zip(coeff,powers):
        if len(result)<len(poly): result.extend([mp.mpc(0)]*(len(poly)-len(result)))
        for i,value in enumerate(poly): result[i]+=scalar*value
    return result

def mp_moments(alpha,degree):
    if abs(alpha)<mp.mpf('1e-80'):
        return [mp.mpf(2)/(k+1) if k%2==0 else mp.mpf(0) for k in range(degree+1)]
    result=[2*mp.sin(alpha)/alpha]
    minus=mp.e**(-1j*alpha); plus=mp.e**(1j*alpha)
    for k in range(1,degree+1):
        result.append((k*result[-1]-(minus-((-1)**k)*plus))/(1j*alpha))
    return result

def mp_transform(xi,families,coefficients,panels,degree):
    half_width=max(width*width for width,_ in families)
    result=mp.mpc(0)
    for panel in range(panels):
        left=-half_width+2*half_width*panel/panels
        right=-half_width+2*half_width*(panel+1)/panels
        centre=(left+right)/2
        half=(right-left)/2
        values=[mp_owner(centre+half*mp.cos(mp.pi*j/degree),families,coefficients) for j in range(degree+1)]
        power=cheb_to_power(cheb_coefficients(values))
        alpha=2*mp.pi*xi*half
        phase=mp.e**(-2j*mp.pi*xi*centre)
        result += half*phase*sum(value*moment for value,moment in zip(power,mp_moments(alpha,degree)))
    return result

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--xi',default='40,80,120,160,200')
    parser.add_argument('--profiles',default='12:12,18:16,24:20')
    args=parser.parse_args()
    _,families,base,corr=f2280.load_owner()
    rows=[]
    mp.mp.dps=100
    for panel_degree in args.profiles.split(','):
        panels,degree=map(int,panel_degree.split(':'))
        for xi_text in args.xi.split(','):
            xi=float(xi_text)
            float_base=f2280.filon_transform(np.array([xi]),families,base,panels,degree)[0]
            float_corr=f2280.filon_transform(np.array([xi]),families,corr,panels,degree)[0]
            exact_base=mp_transform(mp.mpf(xi_text),families,base,panels,degree)
            exact_corr=mp_transform(mp.mpf(xi_text),families,corr,panels,degree)
            rows.append({'panels':panels,'degree':degree,'xi':xi,'base_abs':float(abs(exact_base)),'corr_abs':float(abs(exact_corr)),'base_rel':float(abs(mp_complex(float_base)-exact_base)/max(abs(exact_base),mp.mpf('1e-300'))),'corr_rel':float(abs(mp_complex(float_corr)-exact_corr)/max(abs(exact_corr),mp.mpf('1e-300')))})
    result={'record':2281,'status':'FILON-FLOAT-ARITHMETIC-AUDIT','certificate':False,'rows':rows,'nonclaims':['selected-point audit is not an infinite-tail certificate','mpmath high precision is not directed interval proof','no hgap supplier, producer GO or RH claim']}
    result['max_base_relative_error']=max(row['base_rel'] for row in rows)
    result['max_corr_relative_error']=max(row['corr_rel'] for row in rows)
    OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'max_base_relative_error':result['max_base_relative_error'],'max_corr_relative_error':result['max_corr_relative_error']}))
if __name__=='__main__': main()

