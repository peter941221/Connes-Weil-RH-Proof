"""2340: recomposed point-plus-panel transfer for exact repaired owner."""
import argparse, hashlib, json, math
from fractions import Fraction
from pathlib import Path
from flint import arb, ctx
import routea_marked_sign_arb_certificate_2337 as certificate
import routea_repair_norm_transfer_2339 as transfer
ROOT = Path(__file__).resolve().parents[1]
PIN = Fraction("2644542.8515")
def ep(value): return certificate.serialize_real(value.upper())
def s_constants():
    e = arb(-30).exp()
    k = arb(30)
    return [e, 60 * e, 3900 * e, 245160 * e,
            (696 * k + 780 * k**2 + 360 * k**3 + 16 * k**4) * e]

def ladder(families, coefficients, radii):
    e=arb(-30).exp(); k=arb(30); s=[e,60*e,3900*e,245160*e,(696*k+780*k**2+360*k**3+16*k**4)*e]; out=[arb(0)]*5
    for (_,theta),coefficient,radius in zip(families,coefficients,radii):
        magnitude=abs(coefficient).upper()
        for order in range(5): out[order]+=magnitude*sum(arb(math.comb(order,i))*abs(theta)**i*s[order-i]/radius**(order-i) for i in range(order+1))
    return out
def run():
    ctx.prec=320; capture,families,stored,_,_=certificate.load_capture(); repair=json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text()); baseline=json.loads((ROOT/"results/2303_corrected_strip_envelope.json").read_text())
    for name,digest in transfer.INPUT_HASHES.items(): transfer.check_hash(ROOT/name,digest)
    exact=[a*a for a,_ in families]; old=[certificate.lift_float(float.fromhex(w)**2) for w,_ in capture["families_hex"]]; rmax=max([certificate.lift_float(baseline["owner"]["rmax"])] + exact + old); dx=2*rmax/(240001-1); rows=[]
    for source in baseline["grid_rows"]:
        sigma=transfer.lift(Fraction(source["j"],100)); weight=(abs(sigma-certificate.lift_float(source["sigma"]))*rmax).exp(); ch={}
        for ci,channel in enumerate(("base","correction")):
            delta=[arb(0)]*3; geom=[arb(0)]*3; ideal=[]
            for i,((_,theta),radius,old_radius) in enumerate(zip(families,exact,old)):
                d=transfer.delta_upper(repair["coefficient_rows"][i],channel); terms,gt=transfer.moment_charges(radius,old_radius,theta,abs(stored[ci][i]).upper(),d,sigma); delta=[a+b for a,b in zip(delta,terms)]; geom=[a+b for a,b in zip(geom,gt)]; ideal.append(abs(stored[ci][i]).upper()+d)
            p="base" if channel=="base" else "corr"; m=ladder(families,ideal,exact); factor=(dx**2/12)*(2*rmax)*(abs(sigma)*rmax).exp(); panels=[factor*(m[o+2]+2*abs(sigma)*m[o+1]+sigma**2*m[o]) for o in (0,2)]
            ch[channel]={"m0":(certificate.lift_float(source["point"][p+"_M0"]+source["panel"][p+"_M0"])*weight+delta[0]+geom[0]).upper(),"d2":(certificate.lift_float(source["point"][p+"_D2"]+source["panel"][p+"_D2"])*weight+delta[2]+geom[2]).upper(),"panel_m0":panels[0].upper(),"panel_d2":panels[1].upper(),"repair_m0":delta[0].upper(),"repair_d2":delta[2].upper(),"geometry_m0":geom[0].upper(),"geometry_d2":geom[2].upper()}
        bound=min((ch["base"]["d2"]*ch["correction"]["m0"]).upper(),(ch["correction"]["d2"]*ch["base"]["m0"]).upper()); rows.append({"j":source["j"],"channels":{n:{k:ep(v) for k,v in d.items()} for n,d in ch.items()},"min_product_upper":ep(bound),"fits_existing_pin":bool(bound<=transfer.lift(PIN))})
    maximum=max(rows,key=lambda row:Fraction(row["min_product_upper"]["upper_exact"])); return {"record":2340,"status":"RECOMPOSED_POINT_PANEL_TRANSFER_ENCLOSED_ONLY","precision_bits":ctx.prec,"source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),"rows":rows,"maximum_node":maximum["j"],"maximum_min_product_upper":maximum["min_product_upper"],"all_nodes_fit_existing_pin":all(row["fits_existing_pin"] for row in rows),"failed_nodes":[row["j"] for row in rows if not row["fits_existing_pin"]],"old_inflation_reused":False,"baseline_continuous_point_plus_panel":True,"owner_transfer_to_live_consumer":False,"producer_go":False,"rh_claim":False}
if __name__=="__main__":
    parser=argparse.ArgumentParser(); parser.add_argument("--output",type=Path,default=ROOT/"results/2340_recomposed_point_panel_transfer.json"); args=parser.parse_args(); result=run(); args.output.write_text(json.dumps(result,indent=2)+"\n"); print(result["all_nodes_fit_existing_pin"],result["failed_nodes"],result["maximum_min_product_upper"]["display"])
