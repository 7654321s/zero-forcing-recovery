"""Check that every negative in the unicyclic census has a size-two killing witness."""

from itertools import combinations
import argparse
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
tools = runpy.run_path(str(HERE / 'verify_twinned_unicyclic.py'))
adjacency = tools['adjacency']
neighbors = tools['neighbors']
verify_certificate = tools['verify_certificate']


def bits(vertices):
    return sum(1 << v for v in vertices)


def find_size_two(adj, completion_time):
    infinity = len(adj) + 1
    times = [completion_time(adj, blue) for blue in range(1 << len(adj))]
    for blue, initial in enumerate(times):
        if initial == infinity or blue.bit_count() < 3:
            continue
        times_after_loss = {1 << v: times[blue ^ (1 << v)] for v in neighbors(blue)}
        peak = max(times_after_loss.values())
        if peak == infinity:
            continue
        for u, v in combinations((loss for loss, t in times_after_loss.items() if t < peak), 2):
            if times[blue ^ u ^ v] == infinity:
                return {'blue': blue, 'killing': u | v,
                        'slow': next(loss for loss, t in times_after_loss.items() if t == peak),
                        'restricted_deadline': max(times_after_loss[u], times_after_loss[v]),
                        'slow_completion_time': peak}
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    census_bytes = (HERE / 'unicyclic-through-11.json').read_bytes()
    graphs = json.loads(census_bytes)['graphs']
    prior_bytes = (HERE / 'twinned-unicyclic-replay.json').read_bytes()
    prior = json.loads(prior_bytes)
    assert prior['input_sha256'] == hashlib.sha256(census_bytes).hexdigest()
    twinned = {row['graph_index']: row for row in prior['witnesses']}
    completion_time = runpy.run_path(str(tools['BASELINE']))['completion_time']
    replacements = []
    reused_census = 0
    checked = 0
    for index, graph in enumerate(graphs):
        if graph['every_minimum_support']:
            continue
        adj = adjacency(graph['order'], graph['edges'])
        census = graph['counterexample']
        if index in twinned:
            cert = twinned[index]
        elif census['minimum_killing_size'] == 2 and census['budget'] == 1:
            cert = {'blue': bits(census['blue']), 'killing': bits(census['minimum_killing']),
                    'slow': bits(census['global_loss']), 'restricted_deadline': census['deadline'],
                    'slow_completion_time': census['global_time']}
            reused_census += 1
        else:
            cert = find_size_two(adj, completion_time)
            assert cert is not None, index
            replacements.append({'graph_index': index, 'order': graph['order'], **cert})
        assert cert['killing'].bit_count() == 2 and cert['slow'].bit_count() == 1
        verify_certificate(completion_time, adj, cert['blue'], cert['killing'], cert['slow'],
                           cert['restricted_deadline'], cert['slow_completion_time'])
        checked += 1
    report = {'status': 'passed', 'census_total': len(graphs), 'size_two_witnesses_replayed': checked,
              'twinned_witnesses': len(twinned), 'twin_free_reused': reused_census,
              'twin_free_replacements': replacements,
              'census_sha256': hashlib.sha256(census_bytes).hexdigest(),
              'twinned_witnesses_sha256': hashlib.sha256(prior_bytes).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
