"""Translate the pinned fork certificate table into Lean data, without trusting its checks."""

import argparse
import hashlib
import json
from pathlib import Path
import runpy


FORK_SHA256 = '952e60f8a0c3007e78719731c08dfa568bdd06910b5b04e5f13ccdabb53fe4f2'
READER_SHA256 = '9178ae6acfa12d5070ba0d4d6fd430a68222285c033de05865760c5b5694c0a1'
HERE = Path(__file__).resolve().parent


def lean_list(values):
    return '[' + ', '.join(str(value) for value in values) + ']'


def clock(vertex, early, late):
    return f'⟨{vertex}, {early}, {late}⟩'


def render_traces(adj, blue, support, suppressed):
    masks = [sum(1 << v for v in neighbors) for neighbors in adj]

    def replay(mask, blocked):
        updates = []
        start = mask
        while True:
            next_mask = mask
            for v, neighbors in enumerate(masks):
                if v == blocked or not mask >> v & 1:
                    continue
                targets = neighbors & ~mask
                if targets and targets & (targets - 1) == 0:
                    next_mask |= targets
            if next_mask == mask:
                break
            updates.append(next_mask)
            mask = next_mask
        label = 'none' if blocked is None else f'some {blocked}'
        return f'⟨{label}, {start}, {lean_list(updates)}⟩'

    starts = sorted({blue, blue & ~support, *(blue & ~(1 << v)
                                            for v in range(len(adj)) if blue >> v & 1)})
    return lean_list([replay(start, None) for start in starts] +
                     [replay(blue, v) for v in sorted(set(suppressed))])


def render_fork(row, reader):
    gaps, depth, lengths = row['gaps'], row['depth'], row['lengths']
    adj, stem, ends = reader['make_base'](gaps, depth, lengths)
    if lengths[0] != (3 if lengths[1:] == [1, 1] else 4):
        raise ValueError(f'Unrecognized fork arm lengths: {lengths}')
    members = reader['vertices']
    blue, killing, slow = members(row['blue']), sorted(members(row['killing'])), row['slow']
    if len(killing) != 2 or any(not 0 <= v < len(adj) for v in [*blue, *killing, slow]):
        raise ValueError('A loss refers to a nonexistent vertex or the support has the wrong size')

    trace = reader['trace']
    restricted = [trace(adj, state) for state in (blue, *(blue - {v} for v in killing))]
    delayed = trace(adj, blue - {slow})
    waiting_set = set(row['waiting'])
    waiting = [clock(v, max(state[v] for state in restricted), delayed[v])
               for v in stem[:-1] if v in waiting_set]
    if len(waiting) != len(row['waiting']):
        raise ValueError('Waiting vertices must be distinct proper ancestors')

    tails = []
    for arm in sorted(row['neutral'] + row['white']):
        v = ends[arm]
        if arm in row['white']:
            tail = clock(v, row['deadlines'][str(arm)], row['delays'][str(arm)])
            tails.append(f'({arm}, .white {tail})')
        else:
            tails.append(f'({arm}, .blue {v})')
    edge = 'none'
    if row['edge'] is not None:
        a, b = sorted(members(row['edge']))
        if not 0 <= a < b < len(adj):
            raise ValueError(f'Invalid inserted edge: {(a, b)}')
        edge = f'some ({a}, {b})'

    key = ', '.join(map(str, [*gaps, depth, *lengths[1:]]))
    order = len(adj)
    vertices = '#' + lean_list(lean_list(sorted(neighbors)) for neighbors in adj)
    witness = ', '.join(map(str, [row['blue'], *killing, slow, row['early'], row['late']]))
    traces = render_traces(adj, row['blue'], row['killing'],
                           waiting_set | {ends[i] for i in row['neutral']})
    return (
        f'  {{ certificate := {{\n'
        f'      layout := ⟨{key}⟩,\n'
        f'      table := ({vertices} : Array (List (Fin {order}))),\n'
        f'      witness := (⟨{witness}⟩ : Witness {order}),\n'
        f'      arms := ({lean_list(tails)} : List (ℕ × TailAudit {order})),\n'
        f'      waiting := ({lean_list(waiting)} : List (Clock {order})),\n'
        f'      splitEdge := ({edge} : Option (Fin {order} × Fin {order})) }},\n'
        f'    traces := ({traces} : List (Replay {order})) }}'
    )


def render_batch(name, rows, offset, reader):
    records = ',\n'.join(render_fork(row, reader) for row in rows)
    return f"""module

public import ForkCertificates

@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing.{name}

/-- Certificate table rows {offset} through {offset + len(rows) - 1}, numbered from zero. -/
def data : List ForkReplay := [
{records}]

theorem checked : data.all ForkReplay.check = true := by decide +kernel

theorem witness_of_mem {{r : ForkReplay}} (member : r ∈ data) :
    let c := r.certificate
    BudgetOnePairWitness
      (adj (tableNeighbors (edgeTable c.layout.order c.layout.edges)))
      (colors c.layout.order c.witness.blue) c.witness.support c.witness.slow c.witness.early :=
  r.certificate.checked_witness (r.checked_certificate (List.all_eq_true.mp checked r member))

end FaultObservationResearch.MaskForcing.{name}

#print axioms FaultObservationResearch.MaskForcing.{name}.witness_of_mem
"""


def render_coverage(batches):
    imports = '\n'.join(f'public import {module}' for module in batches)
    groups = ' ++\n  '.join(f'{module}.data' for module in batches)
    checks = ',\n    '.join(f'{module}.checked' for module in batches)
    return f"""module

{imports}

@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 24000000
set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

def certifiedForks : List ForkReplay :=
  {groups}

theorem certified_fork_count : certifiedForks.length = 670 := by decide

theorem certified_fork_layouts : certifiedForks.map ForkReplay.layout = forkLayouts := by
  decide

theorem certified_forks_checked : certifiedForks.all ForkReplay.check = true := by
  simp only [certifiedForks, List.all_append,
    {checks}, Bool.and_self]

theorem fork_cases_have_certificates (layout : ForkLayout) (valid : layout.valid) :
    ∃ c : ForkCertificate, c.layout = layout ∧ c.check = true := by
  have h := (forkLayout_mem_iff layout).mpr valid
  rw [← certified_fork_layouts] at h
  obtain ⟨r, member, shape⟩ := List.mem_map.mp h
  exact ⟨r.certificate, shape,
    r.checked_certificate (List.all_eq_true.mp certified_forks_checked r member)⟩

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.certified_fork_count
#print axioms FaultObservationResearch.MaskForcing.fork_cases_have_certificates
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=HERE / 'adjacent-fork-exploration-03.json')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--batch-size', type=int, default=10)
    parser.add_argument('--limit', type=int, help='write only the first N base certificates')
    args = parser.parse_args()
    if args.batch_size <= 0 or args.limit is not None and args.limit <= 0:
        parser.error('batch size and optional limit must be positive')

    data = args.data.read_bytes()
    reader_source = HERE / 'verify_adjacent_fork_bases.py'
    if hashlib.sha256(data).hexdigest() != FORK_SHA256:
        raise ValueError('The certificate table differs from the published table')
    if hashlib.sha256(reader_source.read_bytes()).hexdigest() != READER_SHA256:
        raise ValueError('The certificate table reader differs from the published reader')
    reader = runpy.run_path(str(reader_source))
    rows = json.loads(data)['proofs']
    if len(rows) != 670:
        raise ValueError('The published table must contain 670 certificates')
    rows = rows[:args.limit]
    args.output.mkdir(parents=True)
    names = []
    for offset in range(0, len(rows), args.batch_size):
        name = f'ForkBatch{offset // args.batch_size:03}'
        rendered = render_batch(name, rows[offset:offset + args.batch_size], offset, reader)
        (args.output / f'{name}.lean').write_bytes(rendered.encode('utf8'))
        names.append(name)
    if len(rows) == 670:
        (args.output / 'ForkCoverage.lean').write_bytes(render_coverage(names).encode('utf8'))
    print(f'Generated Lean inputs for {len(rows)} fork certificates in {args.output}')


if __name__ == '__main__':
    main()
