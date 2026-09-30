"""2288: sampled classical GL remainder price.

This is a feasibility screen for the next missing layer in 2287. It uses the
classical Gauss-Legendre derivative remainder coefficient and sampled high
precision derivatives of the full corrected-owner transform integrand. Sampled
maxima are not uniform bounds and cannot close hgap.
"""
import argparse,json,math
from pathlib import Path
import sys
import mpmath as mp
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import routea_phase_centered_filon_tail_screen_2280 as f
OUT=ROOT/'results/2288_gl_remainder_price.json'

def owner(y,families,coefficients):
    total=mp.mpc(0)
    for coefficient,(width,theta) in zip(coefficients,families):
        radius=mp.mpf(repr(width))**2; q=1-(y/radius)**2
        if q>0:
            c=mp.mpc(mp.mpf(repr(float(coefficient.real))),mp.mpf(repr(float(coefficient.imag))))
            total += c*mp.exp(-30/q)*mp.exp((mp.mpf('.5')+1j*mp.mpf(repr(theta)))*y)
    return total

def gl_coeff(order,length):
    return length**(2*order+1)*(math.factorial(order)**4)/((2*order+1)*(math.factorial(2*order)**3))

def price(xi,families,coefficients,panels,order,samples):
    half=max(w*w for w,_ in families); length=2*half/panels; derivative_order=2*order; vals=[]
    for panel in range(panels):
        left=-half+panel*length; right=left+length
        for index in range(samples):
            y=left+(index+.5)*length/samples
            z=mp.diff(lambda t: owner(t,families,coefficients)*mp.exp(-2j*mp.pi*mp.mpf(repr(xi))*t),mp.mpf(repr(y)),derivative_order)
            vals.append(abs(z))
    max_deriv=max(vals); bound=panels*gl_coeff(order,length)*max_deriv
    return {'panels':panels,'order':order,'xi':xi,'derivative_order':derivative_order,'panel_length':length,'sampled_derivative_max':float(max_deriv),'sampled_GL_remainder_bound':float(bound)}

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--samples',type=int,default=3); parser.add_argument('--xis',default='40,120,200'); parser.add_argument('--profiles',default='8:8,8:16,16:8,16:16'); args=parser.parse_args()
    _,families,base,corr=f.load_owner(); mp.mp.dps=45; rows=[]
    for xi_text in args.xis.split(','):
        xi=float(xi_text)
        for item in args.profiles.split(','):
            panels,order=map(int,item.split(':'))
            rows.append({'base':price(xi,families,base,panels,order,args.samples),'corr':price(xi,families,corr,panels,order,args.samples)})
    result={'record':2288,'status':'GL-REMAINDER-SAMPLED-PRICE','certificate':False,'hgap_closed':False,'rows':rows,'nonclaims':['sampled derivative maxima are not uniform bounds','classical GL remainder formula is only priced, not certified for this owner','finite xi window only','no hgap supplier, producer GO or RH claim']}
    result['max_base_price']=max(r['base']['sampled_GL_remainder_bound'] for r in rows); result['max_corr_price']=max(r['corr']['sampled_GL_remainder_bound'] for r in rows)
    OUT.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps({'max_base_price':result['max_base_price'],'max_corr_price':result['max_corr_price']}))
if __name__=='__main__': main()
