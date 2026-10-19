#!/usr/bin/env python3
import json,re
from fractions import Fraction
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def parse_list(src,name,next_name):
    block=src.split(f'def {name}')[1].split(f'def {next_name}')[0].split('theorem ')[0]
    return [Fraction(int(a),int(b)) for a,b in re.findall(r'\((-?\d+) : ℚ\) / (\d+)',block)]
def main():
    src=(ROOT/'ConnesWeilRH/Dev/C1RouteARepairedOwnerChunkArithmetic3049.lean').read_text(encoding='utf-8')
    d=json.loads((ROOT/'results/3048_cast_owner_chunk_sums.json').read_text())
    minus=parse_list(src,'record3049_minus_chunks','record3049_plus_chunks')
    plus=parse_list(src,'record3049_plus_chunks','theorem record3049_plus_chunks_sum')
    expected={s:[Fraction(c['sum_exact']) for c in d['chunks'] if c['sigma']==s] for s in ('-1/2','1/2')}
    assert minus==expected['-1/2'] and plus==expected['1/2']
    out={'status':'LEAN_CHUNK_PROJECTION_SOURCE_PASS','minus_count':len(minus),'plus_count':len(plus),'all_640_exact_values_match':True,'lean_compiled':False}
    print(json.dumps(out,indent=2))
if __name__=='__main__': main()
