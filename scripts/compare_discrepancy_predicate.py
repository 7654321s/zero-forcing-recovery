"""Separate the paper's minimum-forcing-set discrepancy from time support under loss."""
from pathlib import Path
from itertools import combinations
import argparse,hashlib,importlib.util,json,sys

ROOT=Path(__file__).resolve().parent.parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,default=ROOT,help='Extracted v1.0.0 source directory')
parser.add_argument('--output',type=Path,default=ROOT/'build/paper-comparison.json')
args=parser.parse_args()
SOURCE=args.source/'scripts/experiment.py'
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('frozen_witness_experiment',SOURCE)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
adj=[set() for _ in range(7)]
for a,b in [(0,1),(1,2),(0,3),(3,4),(0,5),(5,6)]:adj[a].add(b);adj[b].add(a)
minimum=[]
for size in range(8):
    minimum=[dict(initial=list(B),time=module.propagation_time(adj,set(B)))
        for B in combinations(range(7),size) if module.propagation_time(adj,set(B)) is not None]
    if minimum:break
low=min(row['time'] for row in minimum);high=max(row['time'] for row in minimum)
assert size==2 and low==high==4
witness=module.witness([2,2,2])
assert witness['killing_number']==2 and witness['global_worst_times'][1]==3 and witness['support_worst_times'][1]==2
result=dict(status='explicit_predicate_separation_verified',graph='St(2,2,2)',vertices=7,
    paper_doi='10.22108/toc.2025.142214.2195',paper_result='Theorem 4.1',
    independent_minimum_zero_forcing_size=size,minimum_zero_forcing_sets=minimum,
    minimum_propagation_time=low,maximum_propagation_time=high,propagation_time_discrepancy=high-low,
    every_minimum_support=False,time_support_counterexample=witness,
    conclusion='Zero discrepancy among minimum zero-forcing sets does not imply EveryMinimumSupport.',
    original_model_or_priority_claim=False,
    witness_script_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
path=args.output
path.parent.mkdir(parents=True,exist_ok=True)
path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='minimum_zero_forcing_sets'},indent=2))
