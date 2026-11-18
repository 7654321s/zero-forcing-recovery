"""Translate path-padding certificates and the fixed-length exception into Lean."""

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import runpy

from generate_fork_lean import clock, lean_list, render_traces


PADDING_SHA256 = '1a2ed5d741435f711b5f437b543575b48f2dc519286e319b9dd3fa4eb5233b1d'
READER_SHA256 = '9a07d456054382b0bf2a47e883ff698ab944c6d6f1079a9320fea5a8e6ba99f1'
HERE = Path(__file__).resolve().parent


def graph(gaps, lengths, reader):
    ring = len(gaps) + sum(gaps)
    branch = reader['branch']
    adj = list(branch['family']['cycle_graph'](ring))
    ends = []
    root = 0
    for gap, length in zip(gaps, lengths):
        ends.append(branch['attach_path'](adj, root, length))
        root += gap + 1
    return adj, ends


def render_edges(gaps, lengths):
    ring = len(gaps) + sum(gaps)
    edges = [(v, (v + 1) % ring) for v in range(ring)]
    site, new = 0, ring
    for gap, length in zip(gaps, lengths):
        previous = site
        for _ in range(length):
            edges.append((previous, new))
            previous, new = new, new + 1
        site += gap + 1
    return lean_list(f'({a}, {b})' for a, b in edges)


def render_input(row, adj, reader):
    members = reader['neighbors']
    killing = list(members(row['killing']))
    slow = list(members(row['slow']))
    if len(killing) != 2 or len(slow) != 1:
        raise ValueError('Expected two support vertices and one delayed vertex')
    if any(not 0 <= v < len(adj) for v in [*members(row['blue']), *killing, *slow]):
        raise ValueError('Certificate refers to a nonexistent vertex')
    witness = ', '.join(map(str, [row['blue'], *killing, *slow,
                                  row['restricted_deadline'], row['slow_completion_time']]))
    table = '#' + lean_list(lean_list(sorted(members(row))) for row in adj)
    return table, witness


def render_padding(row, reader):
    gaps, lengths = row['gaps'], row['minimum_lengths']
    adj, ends = graph(gaps, lengths, reader)
    table, witness = render_input(row, adj, reader)
    order = len(adj)
    tails = []
    for arm in sorted(row['neutral'] + row['white']):
        v = ends[arm]
        if arm in row['white']:
            bound = clock(v, row['boundary_deadlines'][str(arm)], row['slow_boundary'][str(arm)])
            tails.append(f'({arm}, .white {bound})')
        else:
            tails.append(f'({arm}, .blue {v})')
    traces = render_traces([list(reader['neighbors'](mask)) for mask in adj],
                           row['blue'], row['killing'], [ends[i] for i in row['neutral']])
    return (
        f'  {{ certificate := {{\n'
        f'      layout := ⟨{lean_list(gaps)}, {lean_list(lengths)}⟩,\n'
        f'      edges := {render_edges(gaps, lengths)}, edgesExact := by with_unfolding_all rfl,\n'
        f'      table := ({table} : Array (List (Fin {order}))),\n'
        f'      witness := (⟨{witness}⟩ : Witness {order}),\n'
        f'      arms := ({lean_list(tails)} : List (ℕ × TailAudit {order})),\n'
        f'      maxima := {lean_list(row["maxima"])} }},\n'
        f'    traces := ({traces} : List (Replay {order})) }}'
    )


def render_batch(name, rows, offset, reader, gaps=None):
    records = ',\n'.join(render_padding(row, reader) for row in rows)
    group_proof = ''
    label = f'Certificate table rows {offset} through {offset + len(rows) - 1}, numbered from zero.'
    if gaps is not None:
        layout_keys = {tuple(row['minimum_lengths']) for row in rows}
        initial_keys = {tuple(min(length, 2) for length in key) for key in layout_keys}
        marks = {(tuple(row['minimum_lengths']), mark) for row in rows for mark in row['maxima']}
        label = f'{len(rows)} certificates for the gap word {lean_list(gaps)}.'
        group_proof = f"""
def group : PaddingGroup where
  gaps := {lean_list(gaps)}
  data := data
  layoutCount := {len(initial_keys)}
  markCount := {len(marks)}
  checked := checked
  covers := by decide +kernel
  layoutCount_ok := by decide +kernel
  markCount_ok := by decide +kernel
"""
    return f"""import PathPaddingCertificates

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing.{name}

/-- {label} -/
def data : List PaddingReplay := [
{records}]

theorem checked : data.all PaddingReplay.check = true := by decide +kernel
{group_proof}

theorem witness_of_mem {{r : PaddingReplay}} (member : r ∈ data) :
    let p := r.certificate
    BudgetOnePairWitness
      (adj (tableNeighbors (edgeTable p.layout.order p.layout.edges)))
      (colors p.layout.order p.witness.blue) p.witness.support p.witness.slow p.witness.early :=
  r.certificate.checked_witness (r.checked_certificate (List.all_eq_true.mp checked r member))

end FaultObservationResearch.MaskForcing.{name}

#print axioms FaultObservationResearch.MaskForcing.{name}.witness_of_mem
"""


def render_special(reader):
    adj, _ = graph([0, 1, 1], [1, 1, 2], reader)
    finder = runpy.run_path(str(HERE / 'verify_size_two_witnesses.py'))
    baseline = runpy.run_path(str(reader['branch']['BASELINE']))
    row = finder['find_size_two'](adj, baseline['completion_time'])
    if row is None:
        raise ValueError('The fixed length-two exception has no budget-one witness')
    table, witness = render_input(row, adj, reader)
    edges = render_edges([0, 1, 1], [1, 1, 2])
    traces = render_traces([list(reader['neighbors'](mask)) for mask in adj],
                           row['blue'], row['killing'], [])
    return f"""import PathPaddingCertificates

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

def specialPaddingWitness : Witness {len(adj)} := ⟨{witness}⟩
def specialPaddingTable : Array (List (Fin {len(adj)})) := {table}
def specialPaddingTraces : List (Replay {len(adj)}) := {traces}
def specialPaddingEdges : List (ℕ × ℕ) := {edges}

theorem specialPaddingEdges_exact : specialPaddingEdges = paddingException.edges := by
  with_unfolding_all rfl

theorem padding_exception_fixed_length :
    BudgetOnePairWitness
      (adj (tableNeighbors (edgeTable paddingException.order paddingException.edges)))
      (colors paddingException.order specialPaddingWitness.blue)
      specialPaddingWitness.support specialPaddingWitness.slow specialPaddingWitness.early := by
  rw [← specialPaddingEdges_exact]
  exact check_replayed_numbered_witness specialPaddingEdges specialPaddingTable specialPaddingWitness
    specialPaddingTraces (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.padding_exception_fixed_length
"""


def render_coverage(batches):
    imports = '\n'.join(f'import {module}' for module in [*batches, 'PaddingSpecial'])
    groups = ',\n  '.join(f'{module}.group' for module in batches)
    return f"""{imports}

set_option maxRecDepth 65536
set_option maxHeartbeats 100000000
set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

def certifiedPaddingGroups : List PaddingGroup := [
  {groups}]

def certifiedPads : List PaddingReplay := certifiedPaddingGroups.flatMap PaddingGroup.data

theorem certified_pad_count : certifiedPads.length = 5087 := by decide +kernel
theorem certified_padding_gap_count : certifiedPaddingGroups.length = 208 := by decide +kernel
theorem certified_padding_gaps : certifiedPaddingGroups.map PaddingGroup.gaps = paddingGapWords := by
  decide +kernel

theorem original_padding_layout_count : shortPathLayouts.length = 4050 := by
  unfold shortPathLayouts
  rw [List.length_flatMap, ← certified_padding_gaps, List.map_map]
  have h : certifiedPaddingGroups.map (fun g => (palettesAt g.gaps).length) =
      certifiedPaddingGroups.map PaddingGroup.layoutCount :=
    List.map_congr_left (fun g _ => g.layoutCount_ok)
  rw [h]
  decide +kernel

theorem original_padding_mark_count : requiredPaddingMarks.length = 10229 := by
  unfold requiredPaddingMarks
  rw [List.length_flatMap, ← certified_padding_gaps, List.map_map]
  have h : certifiedPaddingGroups.map (fun g => (requiredAt g.gaps).length) =
      certifiedPaddingGroups.map PaddingGroup.markCount :=
    List.map_congr_left (fun g _ => g.markCount_ok)
  rw [h]
  decide +kernel

theorem padding_cases_have_certificates (key : MarkedLayout)
    (member : key ∈ requiredPaddingMarks) :
    ∃ c : PaddingCertificate, key ∈ c.marked ∧ c.check = true := by
  obtain ⟨gaps, hGaps, hMark⟩ := List.mem_flatMap.mp member
  rw [← certified_padding_gaps] at hGaps
  obtain ⟨group, _, hShape⟩ := List.mem_map.mp hGaps
  exact group.covered_witness key (hShape.symm ▸ hMark)

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.certified_pad_count
#print axioms FaultObservationResearch.MaskForcing.certified_padding_gap_count
#print axioms FaultObservationResearch.MaskForcing.original_padding_layout_count
#print axioms FaultObservationResearch.MaskForcing.original_padding_mark_count
#print axioms FaultObservationResearch.MaskForcing.padding_cases_have_certificates
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--batch-size', type=int, default=20)
    parser.add_argument('--limit', type=int, help='write only the first N certificates')
    args = parser.parse_args()
    if args.batch_size <= 0 or args.limit is not None and args.limit <= 0:
        parser.error('batch size and optional limit must be positive')

    data = (HERE / 'path-padding-reduction-replay.json').read_bytes()
    reader_source = HERE / 'verify_path_padding_coverage.py'
    if hashlib.sha256(data).hexdigest() != PADDING_SHA256:
        raise ValueError('The padding table differs from the published table')
    if hashlib.sha256(reader_source.read_bytes()).hexdigest() != READER_SHA256:
        raise ValueError('The padding reader differs from the published reader')
    reader = runpy.run_path(str(reader_source))
    rows = json.loads(data)['certificates']
    if len(rows) != 5087:
        raise ValueError('The published table must contain 5,087 certificates')
    rows = rows[:args.limit]
    args.output.mkdir(parents=True)
    names = []
    if len(rows) == 5087:
        groups = defaultdict(list)
        for row in rows:
            groups[tuple(row['gaps'])].append(row)
        for i, gaps in enumerate(sorted(groups, key=lambda gs: (len(gs), gs))):
            name = f'PaddingBatch{i:03}'
            rendered = render_batch(name, groups[gaps], 0, reader, gaps)
            (args.output / f'{name}.lean').write_bytes(rendered.encode('utf8'))
            names.append(name)
    else:
        for offset in range(0, len(rows), args.batch_size):
            name = f'PaddingBatch{offset // args.batch_size:03}'
            rendered = render_batch(name, rows[offset:offset + args.batch_size], offset, reader)
            (args.output / f'{name}.lean').write_bytes(rendered.encode('utf8'))
    (args.output / 'PaddingSpecial.lean').write_bytes(render_special(reader).encode('utf8'))
    if len(rows) == 5087:
        (args.output / 'PaddingCoverage.lean').write_bytes(render_coverage(names).encode('utf8'))
    print(f'Generated Lean inputs for {len(rows)} padding certificates in {args.output}')


if __name__ == '__main__':
    main()
