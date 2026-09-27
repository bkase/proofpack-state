#!/usr/bin/env python3
"""Small specification oracle, NOT a Bend implementation or a formal proof.

Run with Python 3.10+: python3 reference_check.py
Checks supplied golden cases, closure certificates, and finite algebra examples.
Only standard-library dependencies. No repository/network/disk mutation.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Hashable, TypeVar

T = TypeVar('T', bound=Hashable)


def closure(roots: set[T], adjacency: dict[T, set[T]]) -> set[T]:
    """Simple visited/frontier reference; reject missing adjacency."""
    if not roots <= adjacency.keys():
        raise ValueError('UnknownRoot')
    seen = set(roots)
    frontier = list(roots)
    while frontier:
        vertex = frontier.pop()
        for target in adjacency[vertex]:
            if target not in adjacency:
                raise ValueError('IncompleteGraph')
            if target not in seen:
                seen.add(target)
                frontier.append(target)
    return seen


def certificate(roots: set[T], adjacency: dict[T, set[T]]) -> tuple[set[T], dict[T, int], dict[T, T]]:
    seen = set(roots)
    ranks = {r: 0 for r in roots}
    predecessor: dict[T, T] = {}
    frontier = list(roots)
    while frontier:
        vertex = frontier.pop()
        for target in adjacency[vertex]:
            if target not in adjacency:
                raise ValueError('IncompleteGraph')
            if target not in seen:
                seen.add(target)
                ranks[target] = ranks[vertex] + 1
                predecessor[target] = vertex
                frontier.append(target)
    return seen, ranks, predecessor


def check_certificate(roots: set[T], adjacency: dict[T, set[T]], candidate: set[T],
                      ranks: dict[T, int], predecessor: dict[T, T]) -> bool:
    if not roots <= candidate or not candidate <= adjacency.keys():
        return False
    if any(type(ranks.get(v)) is not int or ranks[v] < 0 for v in candidate):
        return False
    for vertex in candidate:
        if not adjacency[vertex] <= candidate:
            return False
        if vertex not in roots:
            parent = predecessor.get(vertex)
            if parent not in candidate or vertex not in adjacency[parent]:
                return False
            if ranks[parent] >= ranks[vertex]:
                return False
    return True


def powerset(values: list[T]) -> list[set[T]]:
    return [{v for i, v in enumerate(values) if bits & (1 << i)}
            for bits in range(1 << len(values))]


def golden_cases(directory: Path) -> int:
    fixture = json.loads((directory / 'fixtures.json').read_text())
    sizes = {n['id']: n['bytes'] for n in fixture['nodes']}
    for case in fixture['cases']:
        adjacency = {n: set() for n in sizes}
        for source, target, label in fixture['edges']:
            if case['policy'] == 'tree-data' and label == 'parent':
                continue
            adjacency[source].add(target)
        roots = set(case['roots'])
        required = closure(roots, adjacency)
        have = set(fixture['inventories'][case['have']])
        missing = required - have
        assert required == set(case['required']), case['name']
        assert missing == set(case['missing']), case['name']
        assert len(missing) == case['missing_count'], case['name']
        assert sum(sizes[x] for x in missing) == case['missing_bytes'], case['name']
        assert (not missing) == case['ready'], case['name']
        candidate, ranks, pred = certificate(roots, adjacency)
        assert check_certificate(roots, adjacency, candidate, ranks, pred)
        # An unrelated member cannot simply be added to an exact certificate.
        if 'orphan' not in candidate:
            bad = candidate | {'orphan'}
            assert not check_certificate(roots, adjacency, bad,
                                         {**ranks, 'orphan': 1}, pred)
    return len(fixture['cases'])


def exhaustive_small_graphs() -> dict[str, int]:
    """Finite evidence: all 512 directed graphs on three vertices, not a proof."""
    vertices = list(range(3))
    sets = powerset(vertices)
    edges = [(a, b) for a in vertices for b in vertices]
    checks = {'graphs': 0, 'root_cases': 0, 'minimality_cases': 0}
    for bits in range(1 << len(edges)):
        adjacency = {v: set() for v in vertices}
        for i, (source, target) in enumerate(edges):
            if bits & (1 << i):
                adjacency[source].add(target)
        closures = {frozenset(s): closure(s, adjacency) for s in sets}
        checks['graphs'] += 1
        for roots in sets:
            c = closures[frozenset(roots)]
            assert roots <= c
            assert closure(c, adjacency) == c
            assert all(adjacency[v] <= c for v in c)
            candidate, ranks, pred = certificate(roots, adjacency)
            assert candidate == c
            assert check_certificate(roots, adjacency, candidate, ranks, pred)
            checks['root_cases'] += 1
            for other in sets:
                assert closure(roots | other, adjacency) == c | closures[frozenset(other)]
                if roots <= other:
                    assert c <= closures[frozenset(other)]
                missing = c - other
                for transfer in sets:
                    assert (c <= other | transfer) == (missing <= transfer)
                    checks['minimality_cases'] += 1
    return checks


def counterexamples_and_bounds() -> None:
    g = {'a': {'x'}, 'b': {'x'}, 'x': set()}
    a, b = {'a'}, {'b'}
    assert closure(a & b, g) != closure(a, g) & closure(b, g)
    assert closure(a - b, g) != closure(a, g) - closure(b, g)
    # Closure cannot be evaluated independently on an induced ordinal tile.
    g2 = {0: {2}, 1: set(), 2: {1}}
    tile = {0, 1}
    induced = {v: g2[v] & tile for v in tile}
    assert closure({0}, g2) & tile != closure({0}, induced)
    # An old Full is not a Full in the extended universe.
    old, new, a = {0, 1}, {0, 1, 2}, {0}
    assert old - a != new - a
    # Tail masking for representative sizes and corrupted high padding bits.
    for n in (0, 1, 31, 32, 33, 4095, 4096, 4097):
        words = (n + 31) // 32
        total = 0
        for i in range(words):
            width = min(32, n - 32 * i)
            mask = (1 << width) - 1
            bits = 0xFFFFFFFF & mask
            total += bits.bit_count()
        assert total == n
    # Unknown required targets must not silently become leaves.
    try:
        closure({'a'}, {'a': {'missing'}})
    except ValueError as error:
        assert str(error) == 'IncompleteGraph'
    else:
        raise AssertionError('Incomplete graph unexpectedly accepted')


def main() -> None:
    directory = Path(__file__).resolve().parent
    registry = json.loads((directory / 'law-registry.json').read_text())
    ids = [law['id'] for law in registry['laws']]
    assert len(ids) == len(set(ids))
    assert all(set(law['depends_on']) <= set(ids) for law in registry['laws'])
    golden = golden_cases(directory)
    exhaustive = exhaustive_small_graphs()
    counterexamples_and_bounds()
    print(json.dumps({'status': 'passed', 'formal_proof': False,
                      'golden_cases': golden, 'law_obligations': len(ids),
                      **exhaustive}, indent=2))


if __name__ == '__main__':
    main()
