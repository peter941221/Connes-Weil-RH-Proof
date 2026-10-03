"""Parameterized same-owner cells with explicit signed evaluator ownership."""
from dataclasses import dataclass
from fractions import Fraction as Q
import json
import re

from generate_complex_exp_node_2541 import ROOT
from format_lean_source_2553 import wrap_source
from generate_boundary_jets_2548 import render as jet
from generate_endpoint_norms_2544 import render as norm
from generate_signed_midpoint_2543 import render as midpoint
from generate_boundary_fourth_2550 import render as fourth
from generate_adaptive_nodes_2542 import render as value
from generate_cell_integral_2546 import render as integral
from validate_adaptive_nodes_2542 import scalar_def


def read(module):
    return (ROOT/f"ConnesWeilRH/Dev/{module}.lean").read_text(encoding="utf-8")


def rename(source,old,record,new,target=2558):
    return re.sub(r"\b"+old+r"(\w*)"+str(record)+r"\b",lambda m:new+m[1]+str(target),source)


def scalar_layout(source):
    return re.sub(r":\s*([ℝℚ])",r": \1",source)


def tag(index,sign):
    assert sign in (1,-1)
    return f"N{index:05d}{'Plus' if sign > 0 else 'Minus'}"


def endpoint(index,sign):
    name = tag(index,sign)
    if index in (2700,2701,5440,10239):
        return "kernel"+name,2555,"C1RouteAKernel"+name+"2555"
    if index == 2702 and sign == 1:
        return "neighborRight",2557,"C1RouteANeighborRight2557"
    return "batch"+name,2558,"C1RouteABatch"+name+"2558"


def endpoint_value(index,sign):
    name = tag(index,sign)
    if index in (2700,2701,5440,10239):
        return "shared"+name,2556,"C1RouteAShared"+name+"2556"
    if index == 2702 and sign == 1:
        return "neighborValueRight",2557,"C1RouteANeighborValueRight2557"
    return "batchValue"+name,2558,"C1RouteABatchValue"+name+"2558"


def render_endpoint(index,sign):
    prefix,record,module = endpoint(index,sign)
    assert record == 2558
    source,_ = jet("Right",grid_order=(Q(index),3),sigma=Q(sign,2),paired=True)
    source = rename(source,"edgeRight",2548,prefix).replace(":= by cbv",":= by decide +kernel")
    return module,wrap_source(source)


def render_value(index,sign):
    prefix,record,module = endpoint_value(index,sign)
    assert record == 2558
    source,info = value(index,sign,shared_node=True,shared_owner=endpoint(index,sign))
    return module,wrap_source(rename(source,"adaptive"+tag(index,sign),2542,prefix)),info


@dataclass(frozen=True)
class Cell:
    index: int
    sign: int

    @property
    def prefix(self):
        return f"batchC{self.index:05d}{'Plus' if self.sign > 0 else 'Minus'}"

    def module(self,part):
        return "C1RouteA"+self.prefix[0].upper()+self.prefix[1:]+part+"2558"

    def render_midpoint(self):
        source,_ = jet("Midpoint",grid_order=(Q(2*self.index+1,2),2),sigma=Q(self.sign,2),paired=True)
        return wrap_source(rename(source,"edgeMidpoint",2548,self.prefix+"Midpoint")
                           .replace(":= by cbv",":= by decide +kernel"))

    def render_norm(self,side):
        parent,record,module = endpoint(self.index+(side == "Right"),self.sign)
        raw = rename(read(module),parent,record,"endpoint"+side,2544)
        source = norm(side,30,source=raw,bits=160,sigma=Q(self.sign,2))
        source = source.replace("C1RouteAEndpoint"+side+"Third2544",module)
        def translate(m):
            suffix = m[1]
            if suffix == "Position" or re.fullmatch(r"P\d{3}(Factor|Center|Error|DerivativeError)",suffix):
                return parent+suffix+str(record)
            return self.prefix+side+suffix+"2558"
        return wrap_source(re.sub(r"\bendpoint"+side+r"(\w*)2544\b",translate,source))

    def render_midpoint_bounds(self):
        raw = rename(read(self.module("Midpoint")),self.prefix+"Midpoint",2558,"midpoint",2543)
        source,upper,charge = midpoint(source=raw,sigma=Q(self.sign,2))
        source = source.replace("C1RouteAMidpointDerivatives2543",self.module("Midpoint"))
        source = rename(source,"midpoint",2543,self.prefix+"Midpoint")
        source = rename(source,"signedMidpoint",2543,self.prefix+"SignedMidpoint")
        source = source.replace("weightedPhysical_second_midpoint_le2543",self.prefix+"PhysicalSecond2558")
        return wrap_source(source),upper,charge

    def render_fourth(self):
        source,_ = fourth(cell_index=self.index,sigma=Q(self.sign,2))
        for side,offset in (("Left",0),("Right",1)):
            parent,record,module = endpoint(self.index+offset,self.sign)
            source = source.replace("C1RouteABoundary"+side+"2548",module)
            source = source.replace("edge"+side+"Position2548",parent+"Position"+str(record))
        source = rename(source,"edgeFourth",2550,self.prefix+"Fourth")
        return wrap_source(source.replace(":= by cbv",":= by decide +kernel"))

    def render_assembly(self):
        source = read("C1RouteABoundaryAssembly2550")
        source = source.replace("C1RouteABoundaryFourth2550",self.module("Fourth"))
        for side in ("Left","Right","Midpoint"):
            source = source.replace("C1RouteABoundary"+side+"Bounds2549",self.module(side+"Bounds"))
        for side,offset in (("Left",0),("Right",1)):
            parent,record,_ = endpoint(self.index+offset,self.sign)
            source = source.replace("edge"+side+"Position2548",parent+"Position"+str(record))
        source = re.sub(r"\bedge(\w*)25(?:48|49|50)\b",lambda m:self.prefix+m[1]+"2558",source)
        if self.sign < 0:
            source = source.replace("(1/2)","(-1/2)")
        return wrap_source(source)

    def render_integral(self):
        norms = [scalar_layout(rename(self.render_norm(side),self.prefix+side,2558,"endpoint"+side,2544))
                 for side in ("Left","Right")]
        fourth_source = scalar_layout(rename(self.render_fourth(),self.prefix+"Fourth",2558,"fourth",2545))
        lp,lr,lm = endpoint_value(self.index,self.sign)
        rp,rr,rm = endpoint_value(self.index+1,self.sign)
        left_upper = scalar_def(read(lm),lp+"Upper"+str(lr))
        right_source = read(rm)
        right_info = dict(upper=str(scalar_def(right_source,rp+"Upper"+str(rr))))
        source,_,info = integral(cell_index=self.index,sources=(*norms,fourth_source),
            midpoint_upper=self.render_midpoint_bounds()[1],left_upper=left_upper,
            right_node=(right_source,right_info),sigma=Q(self.sign,2))
        for i in range(30):
            replacement = f"""    unfold thirdCellTerm2544
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP{i:03d}NormUpper2544, endpointRightP{i:03d}NormUpper2544,
      {self.prefix}FourthUpper2558, fourthP{i:03d}Upper2545,
      endpointLeftPosition2544, endpointRightPosition2544]
"""
            pattern = r"    unfold thirdCellTerm2544\n    have h := fourthP"+f"{i:03d}"+r"Bound2545\n.*?    linarith\n"
            source,count = re.subn(pattern,replacement,source,count=1,flags=re.S)
            assert count == 1
        for old,new in {
            "C1RouteAFourthEnvelope2545":self.module("Assembly"),
            "C1RouteACellRight2546":rm,"C1RouteAAdaptiveN05440Plus2542":lm,
            "thirdCellTerm2544":self.prefix+"ThirdCell2558",
            "thirdAggregateUpper2544":self.prefix+"ThirdAggregate2558",
            "curvature_after_endpoints2544":self.prefix+"Curvature_bound2558",
            "signedMidpointUpper2543":self.prefix+"SignedMidpointUpper2558",
        }.items():
            source = source.replace(old,new)
        for side,offset in (("Left",0),("Right",1)):
            parent,record,_ = endpoint(self.index+offset,self.sign)
            source = source.replace("endpoint"+side+"Position2544",parent+"Position"+str(record))
            source = rename(source,"endpoint"+side,2544,self.prefix+side)
        source = rename(source,"adaptiveN05440Plus",2542,lp,lr)
        source = rename(source,"adaptiveN05441Plus",2542,rp,rr)
        source = rename(source,"fourth",2545,self.prefix+"Fourth")
        source = rename(source,"cell",2546,self.prefix+"Cell")
        return wrap_source(source),info


def write(module,source):
    (ROOT/f"ConnesWeilRH/Dev/{module}.lean").write_text(source,encoding="utf-8",newline="\n")


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--start",type=int,default=2700)
    parser.add_argument("--cells",type=int,default=2)
    parser.add_argument("--sign",type=int,choices=(-1,1),default=-1)
    args = parser.parse_args()
    assert args.cells > 0 and 0 <= args.start < args.start+args.cells <= 10240
    for index in range(args.start,args.start+args.cells+1):
        if endpoint(index,args.sign)[1] == 2558:
            module,source = render_endpoint(index,args.sign)
            write(module,source)
            module,source,_ = render_value(index,args.sign)
            write(module,source)
    reports = []
    for index in range(args.start,args.start+args.cells):
        cell = Cell(index,args.sign)
        write(cell.module("Midpoint"),cell.render_midpoint())
        for side in ("Left","Right"):
            write(cell.module(side+"Bounds"),cell.render_norm(side))
        write(cell.module("MidpointBounds"),cell.render_midpoint_bounds()[0])
        write(cell.module("Fourth"),cell.render_fourth())
        write(cell.module("Assembly"),cell.render_assembly())
        source,info = cell.render_integral()
        write(cell.module("Integral"),source)
        reports.append(dict(index=index,sign=args.sign,**info))
        print(reports[-1],flush=True)
    (ROOT/"results/2558_signed_cell_inputs.json").write_text(json.dumps(reports,indent=2)+"\n")
