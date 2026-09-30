"""2282: high-precision Chebyshev-basis Filon stability screen."""
import argparse, json, math
from pathlib import Path
import sys
import mpmath as mp
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import routea_phase_centered_filon_tail_screen_2280 as f2280
OUT=ROOT/'results/2282_chebyshev_basis_filon_screen.json'

def mc(z): return mp.mpc(mp.mpf(repr(float(z.real))),mp.mpf(repr(float(z.imag))))
def owner(y,families,coefficients):
    total=mp.mpc(0)
    for coefficient,(width,theta) in zip(coefficients,families):
        q=1-(y/mp.mpf(repr(width))**2)**2
        if q>0: total += mc(coefficient)*mp.exp(-30/q)*mp.exp((mp.mpf('.5')+1j*mp.mpf(repr(theta)))*y)
    return total

def cheb_coeff(values):
    n=len(values)-1; out=[]
    for k in range(n+1):
        total=mp.mpc(0)
        for j,value in enumerate(values):
            weight=mp.mpf('.5') if j in (0,n) else 1
            total += weight*value*mp.cos(mp.pi*k*j/n)
        out.append(total/n if k==0 else 2*total/n)
    return out

def power_cheb(k):
    if k==0:return [mp.mpf(1)]
    if k==1:return [mp.mpf(0),mp.mpf(1)]
    a=[mp.mpf(1)]; b=[mp.mpf(0),mp.mpf(1)]
    for _ in range(2,k+1):
        c=[mp.mpf(0)]*(len(b)+1)
        for i,x in enumerate(b): c[i+1]+=2*x
        for i,x in enumerate(a): c[i]-=x
        a,b=b,c
    return b

def moments(alpha,degree):
    if abs(alpha)<mp.mpf('1e-70'):
        power=[mp.mpf(2)/(j+1) if j%2==0 else 0 for j in range(degree+1)]
    else:
        power=[2*mp.sin(alpha)/alpha]
        minus=mp.exp(-1j*alpha); plus=mp.exp(1j*alpha)
        for j in range(1,degree+1): power.append((j*power[-1]-(minus-((-1)**j)*plus))/(1j*alpha))
    result=[]
    for k in range(degree+1):
        result.append(sum(coef*power[j] for j,coef in enumerate(power_cheb(k))))
    return result

def transform(xi,families,coefficients,panels,degree):
    half_width=max(width*width for width,_ in families); result=mp.mpc(0)
    for panel in range(panels):
        left=-half_width+2*half_width*panel/panels; right=-half_width+2*half_width*(panel+1)/panels
        centre=(left+right)/2; half=(right-left)/2
        values=[owner(centre+half*mp.cos(mp.pi*j/degree),families,coefficients) for j in range(degree+1)]
        coefficients_cheb=cheb_coeff(values); osc=moments(2*mp.pi*xi*half,degree)
        result += half*mp.exp(-2j*mp.pi*xi*centre)*sum(a*b for a,b in zip(coefficients_cheb,osc))
    return result

def run(xi_values,families,coefficients,panels,degree):
    return np.array([complex(transform(mp.mpf(repr(float(x))),families,coefficients,panels,degree)) for x in xi_values])

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--xi',default='40,80,120,160,200')
    parser.add_argument('--profiles',default='12:12,18:16,24:20')
    args=parser.parse_args()
    _,families,base,corr=f2280.load_owner(); mp.mp.dps=80
    xi=[float(x) for x in args.xi.split(',')]
    readings=[]
    for item in args.profiles.split(','):
        panels,degree=map(int,item.split(':'))
        bt=run(xi,families,base,panels,degree); ct=run(xi,families,corr,panels,degree)
        readings.append({'panels':panels,'degree':degree,'xi':xi,'base_abs':[float(abs(x)) for x in bt],'corr_abs':[float(abs(x)) for x in ct]})
    changes=[]
    for i in range(len(readings)-1):
        next_row=readings[i+1]; current=readings[i]
        base_change=max(abs(next_row['base_abs'][j]-current['base_abs'][j])/max(next_row['base_abs'][j],1e-300) for j in range(len(xi)))
        corr_change=max(abs(next_row['corr_abs'][j]-current['corr_abs'][j])/max(next_row['corr_abs'][j],1e-300) for j in range(len(xi)))
        changes.append({'from':current['degree'],'to':next_row['degree'],'max_base_relative_change':base_change,'max_corr_relative_change':corr_change})
    result={'record':2282,'status':'CHEBYSHEV-BASIS-FILON-SCREEN','certificate':False,'hgap_closed':False,'readings':readings,'profile_refinement':changes,'trust_status':'CHEBYSHEV-MP-STABLE-POINT-SCREEN' if max(max(x['max_base_relative_change'],x['max_corr_relative_change']) for x in changes)<1e-3 else 'CHEBYSHEV-MP-UNTRUSTED','nonclaims':['selected xi points are not an infinite-tail certificate','high precision is not a directed interval enclosure','no hgap supplier, producer GO or RH claim']}
    OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8'); print(json.dumps({'trust_status':result['trust_status'],'profile_refinement':changes}))
if __name__=='__main__': main()
