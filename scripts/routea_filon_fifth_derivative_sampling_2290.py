"""2290: panelwise fifth-derivative sampling refinement for Filon 24:4."""
import argparse,json,math
from pathlib import Path
import sys
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import routea_filon_amplitude_remainder_price_2289 as r
import routea_phase_centered_filon_tail_screen_2280 as f2280
OUT=ROOT/'results/2290_filon_fifth_derivative_sampling.json'

def refined(families,coefficients,panels,samples):
    half=max(w*w for w,_ in families); length=2*half/panels; order=5; panel_rows=[]
    for panel in range(panels):
        left=-half+panel*length; vals=[]
        for i in range(samples):
            y=left+(i+.5)*length/samples
            vals.append(float(abs(mp.diff(lambda t:r.owner(t,families,coefficients),mp.mpf(repr(y)),order))))
        panel_rows.append({'panel':panel,'sampled_max':max(vals),'sampled_arg':int(max(range(len(vals)),key=lambda i:vals[i]))})
    total=panels*(length/2)**order/math.factorial(order)*max(row['sampled_max'] for row in panel_rows)
    return {'samples_per_panel':samples,'global_sampled_max':max(row['sampled_max'] for row in panel_rows),'amplitude_remainder_price':total,'panel_rows':panel_rows}

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--samples',default='3,9,33'); args=parser.parse_args()
    _,families,base,corr=f2280.load_owner(); mp.mp.dps=45; rows=[]
    for samples in [int(x) for x in args.samples.split(',')]:
        rows.append({'base':refined(families,base,24,samples),'corr':refined(families,corr,24,samples)})
    result={'record':2290,'status':'FILON-FIFTH-DERIVATIVE-SAMPLING','certificate':False,'hgap_closed':False,'profiles':{'panels':24,'degree':4,'derivative_order':5},'rows':rows,'nonclaims':['sampled maxima are not uniform derivative enclosures','no interval panel certificate','finite window and infinite tail remain separate','no hgap supplier, producer GO or RH claim']}
    result['base_refinement']=[rows[i]['base']['amplitude_remainder_price']/rows[i-1]['base']['amplitude_remainder_price'] for i in range(1,len(rows))]; result['corr_refinement']=[rows[i]['corr']['amplitude_remainder_price']/rows[i-1]['corr']['amplitude_remainder_price'] for i in range(1,len(rows))]
    OUT.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps({'base_prices':[x['base']['amplitude_remainder_price'] for x in rows],'corr_prices':[x['corr']['amplitude_remainder_price'] for x in rows]}))
if __name__=='__main__': main()


