"""Cross-check the insertion theorem by growing the small labelled families."""
import argparse
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


@cache
def inputs(n):
    return tuple(sum(1 << r for r in range(1 << n) if r >> i & 1) for i in range(n))


@cache
def target(n):
    return sum(1 << r for r in range(1 << n) if (0xfeea8880 >> ((r & 15) + 16 * int(r >= 16))) & 1)


def canonical(n, gates, output):
    mapped = {i: i for i in range(n)}
    pending = set(range(n, n+len(gates)))
    normalized = []
    while pending:
        ready = []
        for j in pending:
            op, a, b = gates[j-n]
            if a in mapped and b in mapped:
                a, b = sorted([mapped[a], mapped[b]])
                ready.append((b, a, op, j))
        b, a, op, j = min(ready)
        normalized.append((op, a, b))
        mapped[j] = n+len(normalized)-1
        pending.remove(j)
    assert mapped[output] == n+len(normalized)-1
    return tuple(normalized)


def graft(n, program, wire, redirected):
    words = list(inputs(n+1))
    gates = []
    remap = {i:i for i in range(n)}

    def add(op, a, b):
        gates.append((op,a,b))
        words.append(words[a] & words[b] if op == '&' else words[a] | words[b])
        return len(words)-1

    new_wire = add('|', n, remap[wire]) if wire < n else None
    for j, (op, a, b) in enumerate(program, n):
        left = new_wire if (j, 0) in redirected else remap[a]
        right = new_wire if (j, 1) in redirected else remap[b]
        remap[j] = add(op, left, right)
        if j == wire:
            new_wire = add('|', n, remap[j])
    output = new_wire if ('out', 0) in redirected else remap[n+len(program)-1]
    if words[output] == target(n+1):
        return canonical(n+1, gates, output)


def successors(n, program):
    ports = defaultdict(list)
    for j, (_, a, b) in enumerate(program, n):
        ports[a].append((j, 0))
        ports[b].append((j, 1))
    ports[n+len(program)-1].append(('out', 0))
    for wire, uses in ports.items():
        for size in range(1, len(uses)+1):
            for subset in combinations(uses,size):
                result = graft(n,program,wire,subset)
                if result is not None:
                    yield result


def profile(n, program):
    twins = set(range(4,n))
    cones = [{i} & twins for i in range(n)]
    depths = [0]*n
    words = list(inputs(n))
    for op, a, b in program:
        cones.append(cones[a] | cones[b] if op == '|' else set())
        depths.append(max(depths[a],depths[b])+1)
        words.append(words[a] | words[b] if op == '|' else words[a] & words[b])
    disjunction = sum(1 << row for row in range(16,1 << n))
    assert twins in cones
    return disjunction in words, depths[-1]


def load(filename):
    programs = json.loads((ROOT / filename).read_text())
    return {tuple(map(tuple,program)) for program in programs}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--twins',type=int,choices=range(2,7),default=4)
    kmax = parser.parse_args().twins
    models = load('cores.json')
    trees = 1
    for k in range(2,kmax+1):
        n = 4+k
        models = {new for old in models for new in successors(n-1,old)}
        if k == 2:
            assert models == load('six-input.json')
        trees *= 2*k-3
        profiles = Counter(profile(n,m) for m in models)
        assert len(models) == 6*(k+1)*trees
        pure = sum(v for (has_wire,_),v in profiles.items() if has_wire)
        assert pure == 12*trees
        print(k, 'twins,',len(models),'minimum networks,',pure,'with a pure OR wire')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without Python optimization.')
    main()
