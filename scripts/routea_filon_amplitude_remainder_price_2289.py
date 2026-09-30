"""2289: phase-aware Filon amplitude-only remainder price.

The oscillatory phase is integrated analytically; the sampled remainder price
uses derivatives of the non-oscillatory owner amplitude only. This is a
feasibility screen, not a uniform enclosure.
"""
import argparse,json,math
from pathlib import Path
import sys
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import routea_phase_centered_filon_tail_screen_2280 as f
OUT=ROOT/'results/2289_filon_amplitude_remainder_price.json'

def owner(y,families,coefficients):
    total=mp.mpc(0)
    for coefficient,(width,theta) in zip(coefficients,families):
        radius=mp.mpf(repr(width))**2; q=1-(y/radius)**2
        if q>0:
            c=mp.mpc(mp.mpf(repr(float(coefficient.real))),mp.mpf(repr(float(coefficient.imag))))
            total += c*mp.exp(-30/q)*mp.exp((mp.mpf('.5')+1j*mp.mpf(repr(theta)))*y)
    return total

def price(families,coefficients,panels,degree,samples):
    half=max(w*w for w,_ in families); length=2*half/panels; order=degree+1; vals=[]
    for panel in range(panels):
        left=-half+panel*length
        for index in range(samples):
            y=left+(index+.5)*length/samples
            vals.append(abs(mp.diff(lambda t: owner(t,families,coefficients),mp.mpf(repr(y)),order)))
    max_deriv=max(vals); bound=panels*(length/2)**order/math.factorial(order)*max_deriv
    return {'panels':panels,'degree':degree,'derivative_order':order,'panel_length':length,'sampled_derivative_max':float(max_deriv),'amplitude_remainder_price':float(bound)}

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--samples',type=int,default=3); parser.add_argument('--profiles',default='12:4,12:6,12:8,24:4,24:6,24:8'); args=parser.parse_args()
    _,families,base,corr=f.load_owner(); mp.mp.dps=45; rows=[]
    for item in args.profiles.split(','):
        panels,degree=map(int,item.split(':')); rows.append({'profile':item,'base':price(families,base,panels,degree,args.samples),'corr':price(families,corr,panels,degree,args.samples)})
    result={'record':2289,'status':'FILON-AMPLITUDE-REMAINDER-PRICE','certificate':False,'hgap_closed':False,'rows':rows,'nonclaims':['sampled amplitude derivatives are not uniform bounds','phase-aware residual price is not a quadrature certificate','finite xi window and infinite tail remain separate','no producer GO or RH claim']}
    result['best_base_price']=min(r['base']['amplitude_remainder_price'] for r in rows); result['best_corr_price']=min(r['corr']['amplitude_remainder_price'] for r in rows)
    OUT.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps({'best_base_price':result['best_base_price'],'best_corr_price':result['best_corr_price']}))
if __name__=='__main__': main()
