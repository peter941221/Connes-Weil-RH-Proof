"""2284: panel-wise independent mpmath quadrature audit.

The previous global mpmath result was not trusted. This record checks each
panel and precision separately before summing, so apparent cancellation can
be distinguished from quadrature drift.
"""
import argparse,json
from pathlib import Path
import sys
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import routea_phase_centered_filon_tail_screen_2280 as f2280
OUT=ROOT/'results/2284_panelwise_mpmath_audit.json'

def owner(y,families,coefficients):
    total=mp.mpc(0)
    for coefficient,(width,theta) in zip(coefficients,families):
        radius=mp.mpf(repr(width))**2; q=1-(y/radius)**2
        if q>0:
            c=mp.mpc(mp.mpf(repr(float(coefficient.real))),mp.mpf(repr(float(coefficient.imag))))
            total += c*mp.exp(-30/q)*mp.exp((mp.mpf('.5')+1j*mp.mpf(repr(theta)))*y)
    return total

def panel_integral(xi,left,right,families,coefficients):
    return mp.quad(lambda y: owner(y,families,coefficients)*mp.exp(-2j*mp.pi*xi*y),[left,right])

def run(xi,panels,families,coefficients,precisions):
    half=max(w*w for w,_ in families); rows=[]
    for precision in precisions:
        mp.mp.dps=precision; values=[]
        for panel in range(panels):
            left=-half+2*half*panel/panels; right=-half+2*half*(panel+1)/panels
            value=panel_integral(mp.mpf(repr(xi)),left,right,families,coefficients)
            values.append(value)
        total=sum(values,mp.mpc(0))
        rows.append({'precision':precision,'total_abs':float(abs(total)),'panel_abs_max':float(max(abs(v) for v in values)),'panel_values':[{'real':float(mp.re(v)),'imag':float(mp.im(v))} for v in values]})
    return rows

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--xi',type=float,default=40.0); parser.add_argument('--panels',type=int,default=8); args=parser.parse_args()
    _,families,base,corr=f2280.load_owner(); result={'record':2284,'status':'PANELWISE-MP-MATH-AUDIT','certificate':False,'hgap_closed':False,'xi':args.xi,'panels':args.panels,'base':run(args.xi,args.panels,families,base,[35,50,70]),'corr':run(args.xi,args.panels,families,corr,[35,50,70]),'nonclaims':['panelwise mpmath is not a directed interval certificate','finite xi sample is not the infinite tail','no hgap supplier, producer GO or RH claim']}
    result['base_precision_movement']=abs(result['base'][2]['total_abs']-result['base'][0]['total_abs'])/max(result['base'][2]['total_abs'],1e-300)
    result['corr_precision_movement']=abs(result['corr'][2]['total_abs']-result['corr'][0]['total_abs'])/max(result['corr'][2]['total_abs'],1e-300)
    result['trust_status']='PANELWISE-MP-STABLE' if max(result['base_precision_movement'],result['corr_precision_movement'])<1e-8 else 'PANELWISE-MP-UNTRUSTED'
    OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8'); print(json.dumps({'trust_status':result['trust_status'],'base_movement':result['base_precision_movement'],'corr_movement':result['corr_precision_movement']}))
if __name__=='__main__': main()

