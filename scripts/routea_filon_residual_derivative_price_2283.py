"""2283: derivative-price screen for local Filon interpolation residuals.

The sampled derivative maxima are not a certificate. The purpose is to price
whether a uniform Lagrange residual enclosure could plausibly fit the tail
budget before implementing a directed derivative bound.
"""
import argparse,json,math
from pathlib import Path
import sys
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import routea_phase_centered_filon_tail_screen_2280 as f2280
OUT=ROOT/'results/2283_filon_residual_derivative_price.json'

def owner_mp(y,families,coefficients):
    total=mp.mpc(0)
    for coefficient,(width,theta) in zip(coefficients,families):
        radius=mp.mpf(repr(width))**2
        q=1-(y/radius)**2
        if q>0:
            c=mp.mpc(mp.mpf(repr(float(coefficient.real))),mp.mpf(repr(float(coefficient.imag))))
            total += c*mp.exp(-30/q)*mp.exp((mp.mpf('.5')+1j*mp.mpf(repr(theta)))*y)
    return total

def price(families,coefficients,panels,degree,samples):
    half_width=max(w*w for w,_ in families); panel_width=2*half_width/panels; derivative_order=degree+1
    maxima=[]
    for panel in range(panels):
        left=-half_width+panel_width*panel; right=left+panel_width
        values=[]
        for index in range(samples):
            y=left+(index+0.5)*panel_width/samples
            value=mp.diff(lambda z: owner_mp(z,families,coefficients),mp.mpf(repr(y)),derivative_order)
            values.append(float(abs(value)))
        maxima.append(max(values))
    local_error=[(panel_width/2)**derivative_order/max(1,math.factorial(derivative_order))*value for value in maxima]
    integral_bound=sum(panel_width*value for value in local_error)
    return {'panels':panels,'degree':degree,'derivative_order':derivative_order,'panel_width':panel_width,'sampled_derivative_max':max(maxima),'interpolation_integral_bound':integral_bound,'max_panel_error':max(local_error)}

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--samples',type=int,default=3); parser.add_argument('--profiles',default='12:12,18:16,24:20'); args=parser.parse_args()
    _,families,base,corr=f2280.load_owner(); mp.mp.dps=50; rows=[]
    for item in args.profiles.split(','):
        panels,degree=map(int,item.split(':'))
        b=price(families,base,panels,degree,args.samples); c=price(families,corr,panels,degree,args.samples)
        rows.append({'profile':f'{panels}:{degree}','base':b,'corr':c})
    result={'record':2283,'status':'FILON-RESIDUAL-DERIVATIVE-PRICE','certificate':False,'hgap_closed':False,'rows':rows,'nonclaims':['sampled derivative maxima are not uniform derivative enclosures','residual price ignores kernel coupling and is only a feasibility screen','no hgap supplier, producer GO or RH claim']}
    OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8'); print(json.dumps({'rows':rows}))
if __name__=='__main__': main()
