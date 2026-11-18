"""Finite reproduction of longest-arm one-short-arm witnesses; not a general proof."""
from datetime import datetime, timezone
from itertools import combinations_with_replacement
from pathlib import Path
import hashlib
import importlib.util
import json
import shutil

ROOT=Path(__file__).resolve().parents[1]
SIMULATOR=ROOT/'scripts/experiment.py'
spec=importlib.util.spec_from_file_location('checked_synchronous_simulator',SIMULATOR)
sim=importlib.util.module_from_spec(spec)
spec.loader.exec_module(sim)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()


def check(lengths):
    assert lengths.count(1)==1 and len(lengths)>=3
    short=lengths.index(1)
    longest=max(range(len(lengths)),key=lengths.__getitem__)
    other=max((i for i in range(len(lengths)) if i not in (short,longest)),key=lengths.__getitem__)
    adjacency=[set() for _ in range(1+sum(lengths))]
    arms=[]
    offset=1
    for length in lengths:
        arm=list(range(offset,offset+length));arms.append(arm)
        for x,y in zip([0]+arm,arm):
            adjacency[x].add(y);adjacency[y].add(x)
        offset+=length
    blue={0,arms[longest][-1]}|{arm[0] for i,arm in enumerate(arms) if i!=longest}
    support={arms[short][0],arms[longest][-1]}
    single=[(sorted(loss),sim.propagation_time(adjacency,blue-loss)) for loss in sim.losses(blue,1)]
    assert sim.propagation_time(adjacency,blue-support) is None
    assert all(t is not None for _,t in single)
    restricted=sim.worst_time(adjacency,blue,support,1)
    unrestricted=sim.worst_time(adjacency,blue,blue,1)
    attaining=sim.propagation_time(adjacency,blue-{arms[other][0]})
    maximum=lengths[longest];second=lengths[other]
    assert restricted==maximum and unrestricted==maximum+second-1 and attaining==unrestricted
    return dict(arm_lengths=list(lengths),vertices=len(adjacency),
        initial_blue=sorted(blue),minimum_killing_support=sorted(support),minimum_killing_cardinality=2,
        deadline=maximum,budget=1,restricted_worst_time=restricted,global_worst_time=unrestricted,
        attaining_loss=[arms[other][0]],single_loss_times=[dict(loss=d,time=t) for d,t in single])


def main():
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S_%fZ')
    run=ROOT/'build'/(stamp+'-one-short-deadline-experiment');run.mkdir(parents=True)
    shutil.copy2(Path(__file__),run/Path(__file__).name)
    shutil.copy2(SIMULATOR,run/'simulator.py')
    cases=[]
    for degree in range(3,7):
        for long_lengths in combinations_with_replacement(range(2,6),degree-1):
            cases.append(check((1,)+long_lengths))
    cases.extend(check((1,m,m)) for m in (8,30,80))
    result=dict(status='finite_one_short_deadline_witnesses_passed',cases=len(cases),
        scope='All sorted vectors with 3..6 arms, exactly one length1 arm, others2..5; additional (1,m,m), m=8,30,80. Chosen longest terminal-seeded arm; all initial losses of size at most one.',
        null_means='infinite propagation time',general_classification_proved=False,
        inputs=[dict(file='scripts/'+Path(__file__).name,sha256=sha(Path(__file__))),
                dict(file=SIMULATOR.relative_to(ROOT).as_posix(),sha256=sha(SIMULATOR))],
        examples=[c for c in cases if c['arm_lengths'] in [[1,2,2],[1,2,5],[1,5,5],[1,8,8],[1,30,30],[1,80,80]]])
    (run/'run_summary.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    record=dict(status=result['status'],run=str(run.relative_to(ROOT)/'run_summary.json'),
                summary_sha256=sha(run/'run_summary.json'),cases=len(cases),general_classification_proved=False)
    (ROOT/'build/latest-one-short.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(record))


if __name__=='__main__':
    main()
