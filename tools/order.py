#!/usr/bin/env python3
"""Topologically order the top-level definitions of a .bend file.

Bend requires a def to be declared above every def that calls it, and rejects
mutual recursion outright. Writing a module in reading order and then
shuffling it by hand is a waste of everyone's time, so this does it: it reads
the call graph of a file's own definitions and emits them in dependency
order, keeping the original relative order wherever the dependencies allow.

A genuine cycle is an error, not something to paper over: Bend forbids mutual
recursion, so a cycle means the code needs restructuring (carry the decision
as a parameter, or return a step constructor the loop matches). The cycle is
printed so it can be fixed rather than hidden.

Usage: tools/order.py FILE.bend [--check]
"""
import re
import sys

DEF = re.compile(r'^(?:@unsafe\s+)?(def|law|type)\s+([A-Za-z_][A-Za-z0-9_.]*)')
CTOR = re.compile(r'^\s\s([A-Z][A-Za-z0-9_.]*)\s*\{')
TOKEN = re.compile(r'[A-Za-z_][A-Za-z0-9_.]*')


def split_blocks(text):
    """Return (preamble, [(name, kind, lines)]) splitting on top-level defs."""
    lines = text.split('\n')
    starts = []
    for i, line in enumerate(lines):
        m = DEF.match(line)
        if m:
            starts.append((i, m.group(2), m.group(1)))
    if not starts:
        return text.split('\n'), []

    def block_begin(idx):
        """Include the comment lines attached directly above a definition."""
        j = idx - 1
        while j >= 0 and lines[j].startswith('#'):
            j -= 1
        return j + 1

    preamble = lines[:block_begin(starts[0][0])]
    blocks = []
    for k, (idx, name, kind) in enumerate(starts):
        beg = block_begin(idx)
        end = block_begin(starts[k + 1][0]) if k + 1 < len(starts) else len(lines)
        blocks.append((name, kind, lines[beg:end]))
    return preamble, blocks


def constructors(blocks):
    """Map each constructor name to the type block that declares it."""
    owner = {}
    for name, kind, body in blocks:
        if kind != 'type':
            continue
        for line in body[1:]:
            m = CTOR.match(line)
            if m:
                owner[m.group(1)] = name
    return owner


def order(path, check_only=False):
    text = open(path).read()
    preamble, blocks = split_blocks(text)
    if not blocks:
        return 0

    names = [b[0] for b in blocks]
    index = {n: i for i, n in enumerate(names)}
    owner = constructors(blocks)

    deps = []
    for i, (name, kind, body) in enumerate(blocks):
        want = set()
        head = body[0] if body else ''
        for line in body:
            for tok in TOKEN.findall(line):
                target = None
                if tok in index:
                    target = tok
                elif tok in owner:
                    target = owner[tok]
                if target is None:
                    continue
                j = index[target]
                if j != i:
                    want.add(j)
        deps.append(want)

    # Stable topological sort: repeatedly take the earliest block whose
    # dependencies are all placed.
    placed = []
    done = set()
    remaining = set(range(len(blocks)))
    while remaining:
        ready = [i for i in sorted(remaining) if deps[i] <= done]
        if not ready:
            cyc = sorted(remaining)
            print('%s: definitions form a cycle; Bend forbids mutual '
                  'recursion.' % path, file=sys.stderr)
            for i in cyc[:12]:
                unmet = sorted(names[j] for j in deps[i] if j not in done)
                print('  %s needs %s' % (names[i], ', '.join(unmet)),
                      file=sys.stderr)
            return 1
        i = ready[0]
        placed.append(i)
        done.add(i)
        remaining.discard(i)

    # Rebuilt from line lists rather than by string joining, so no separator
    # can be lost or doubled at a block boundary.
    lines = list(preamble)
    for i in placed:
        lines.extend(blocks[i][2])
    while len(lines) > 1 and lines[-1] == '' and lines[-2] == '':
        lines.pop()
    out = '\n'.join(lines)
    if out == text:
        return 0
    if check_only:
        print('%s: definitions are out of dependency order' % path,
              file=sys.stderr)
        return 1
    open(path, 'w').write(out)
    print('%s: reordered' % path)
    return 0


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    check = '--check' in sys.argv
    sys.exit(max(order(p, check) for p in args) if args else 2)
