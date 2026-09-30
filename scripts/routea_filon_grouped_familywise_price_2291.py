"""2291: familywise versus grouped fifth-derivative price."""
import argparse,json,math
from pathlib import Path
import sys
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import routea_filon_amplitude_remainder_price_2289 as base
import routea_phase_centered_filon_tail_screen_2280 as owner_mod
OUT=ROOT/'results/2291_filon_grouped_vs_familywise_price.json'

def term(y,width,theta,coefficient):
    radius=mp.mpf(repr(width))**2; q=1-(y/radius)**2
    if q<=0:return mp.mpc(0)
    c=mp.mpc(mp.mpf(repr(float(coefficient.real))),mp.mpf(repr(float(coefficient.imag))))
    return c*mp.exp(-30/q)*mp.exp((mp.mpf('.5')+1j*mp.mpf(repr(theta)))*y)

def price(families,coefficients,panels,samples):
    half=max(w*w for w,_ in families); length=2*half/panels; grouped=[]; family_total=0.0
    for panel in range(panels):
        left=-half+panel*length
        for index in range(samples):
            y=left+(index+.5)*length/samples
            grouped.append(abs(mp.diff(lambda t: base.owner(t,families,coefficients),mp.mpf(repr(y)),5)))
            for width,theta,coefficient in zip([x[0] for x in families],[x[1] for x in families],coefficients):
                family_total += float(abs(mp.diff(lambda t,w=width,th=theta,c=coefficient: term(t,w,th,c),mp.mpf(repr(y)),5)))
    shape=(length/2)**5/math.factorial(5)
    return {'grouped_price':panels*shape*float(max(grouped)),'familywise_price':panels*shape*family_total/samples,'grouped_sampled_max':float(max(grouped))}

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--samples',type=int,default=33); args=parser.parse_args()
    _,families,base,corr=owner_mod.load_owner(); mp.mp.dps=45
    rows=[{'channel':'base','values':price(families,base,24,args.samples)},{'channel':'corr','values':price(families,corr,24,args.samples)}]
    result={'record':2291,'status':'FILON-GROUPED-VS-FAMILYWISE-PRICE','certificate':False,'hgap_closed':False,'rows':rows,'nonclaims':['sampled maxima are not uniform bounds','familywise price is a feasibility comparison, not a certificate','no hgap supplier, producer GO or RH claim']}
    result['familywise_to_grouped']={r['channel']:r['values']['familywise_price']/max(r['values']['grouped_price'],1e-300) for r in rows}
    OUT.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result['familywise_to_grouped']))
if __name__=='__main__': main()
