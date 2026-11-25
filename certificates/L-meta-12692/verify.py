"""Verify the two labelled catalogues and reconstruct their LRAT input files."""
from itertools import combinations
from pathlib import Path
from collections import Counter
import argparse
import json

ROOT = Path(__file__).resolve().parent


class Encoding:
    def __init__(self):
        self.variables = {}
        self.clauses = []

    def variable(self, *key):
        if key not in self.variables:
            self.variables[key] = len(self.variables) + 1
        return self.variables[key]

    def one_of(self, choices):
        self.clauses.append(choices)
        self.clauses.extend([-a, -b] for a, b in combinations(choices, 2))

    def add_circuit_constraints(self, inputs, output, target, rows):
        var = self.variable
        clauses = self.clauses
        for i in range(inputs):
            for row in rows:
                wire = var('wire', i, row)
                clauses.append([wire if row & (1 << i) else -wire])
        for node in range(inputs, output + 1):
            op = var('and', node)
            for side in (0, 1):
                self.one_of([var('src', node, side, i) for i in range(node)])
                for i in range(node):
                    selector = var('src', node, side, i)
                    for row in rows:
                        port = var('port', node, side, row)
                        source = var('wire', i, row)
                        clauses.extend([[-selector, -port, source], [-selector, port, -source]])
            for left in range(node):
                for right in range(left + 1):
                    clauses.append([-var('src', node, 0, left), -var('src', node, 1, right)])
            for row in rows:
                a = var('port', node, 0, row)
                b = var('port', node, 1, row)
                out = var('wire', node, row)
                clauses.extend([[-op, -out, a], [-op, -out, b], [-op, out, -a, -b],
                                [op, out, -a], [op, out, -b], [op, -out, a, b]])
        for row in rows:
            wire = var('wire', output, row)
            clauses.append([wire if target >> row & 1 else -wire])

    def dimacs(self):
        header = f'p cnf {len(self.variables)} {len(self.clauses)}\n'
        return header + ''.join(' '.join(map(str, clause)) + ' 0\n' for clause in self.clauses)


def boundary(inputs, target):
    true = {i for i in range(1 << inputs) if target >> i & 1}
    false = set(range(1 << inputs)) - true
    assert all(a & b != a for a in true for b in false)
    mins = sorted(r for r in true if not any(t != r and t & r == t for t in true))
    maxs = sorted(r for r in false if not any(t != r and t & r == r for t in false))
    return mins + maxs


def add_topological_order(enc, n, output):
    var = enc.variable
    def port(j, side, i):
        return var('src', j, side, i)
    for j in range(n, output):
        k = j + 1
        for x in range(j):
            for v in range(x):
                enc.clauses.append([-port(j, 1, x), -port(k, 1, v)])
            for y in range(x):
                for u in range(y):
                    enc.clauses.append([-port(j, 1, x), -port(k, 1, x),
                                        -port(j, 0, y), -port(k, 0, u)])
                equal = [-port(j, 1, x), -port(k, 1, x), -port(j, 0, y), -port(k, 0, y)]
                enc.clauses.append(equal + [var('and', j)])
                enc.clauses.append(equal + [-var('and', k)])
    for i in range(output):
        enc.clauses.append([port(j, side, i) for j in range(max(i+1, n), output+1)
                            for side in (0, 1)])


def verify(inputs, catalogue, target):
    output = 2 * inputs + 2
    enc = Encoding()
    enc.add_circuit_constraints(inputs, output, target, boundary(inputs, target))
    add_topological_order(enc, inputs, output)
    seen = set()
    depths = Counter()
    direct = 0
    for program in catalogue:
        key = tuple(map(tuple, program))
        assert key not in seen
        seen.add(key)
        assert len(program) == output-inputs+1
        values = [sum(1 << r for r in range(1 << inputs) if r >> i & 1) for i in range(inputs)]
        levels = [0] * inputs
        cones = [{i} for i in range(inputs)]
        reads = set()
        order = []
        clause = []
        for node, (op, a, b) in enumerate(program, inputs):
            assert 0 <= a < b < node and op in ('&', '|')
            order.append((b, a, op))
            reads.update([a,b])
            values.append(values[a] & values[b] if op == '&' else values[a] | values[b])
            levels.append(max(levels[a], levels[b]) + 1)
            cones.append(set() if op == '&' else cones[a] | cones[b])
            choice = enc.variable('and', node)
            clause.extend([-choice if op=='&' else choice, -enc.variable('src',node,0,a),
                           -enc.variable('src',node,1,b)])
        assert order == sorted(order) and len(set(order)) == len(order)
        assert reads == set(range(output)) and values[-1] == target
        assert len(set(values)) == len(values)
        if inputs == 6:
            assert any({4,5} <= cone for cone in cones)
            direct += ['|',4,5] in program
        depths[levels[-1]] += 1
        enc.clauses.append(clause)
    print(inputs, 'inputs,', len(seen), 'networks; depths', sorted(depths.items()))
    if inputs == 6:
        print(direct, 'direct twin OR gates among these networks')
    return enc.dimacs().encode('ascii')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--six-cnf', type=Path, help='also write the independent six-input CNF')
    args = parser.parse_args()
    cores = json.loads((ROOT / 'cores.json').read_text())
    six = json.loads((ROOT / 'six-input.json').read_text())
    assert verify(5, cores, 0xfeea8880) == (ROOT / 'cores.cnf').read_bytes()
    dimacs = verify(6, six, 0xfeeafeeafeea8880)
    if args.six_cnf:
        args.six_cnf.write_bytes(dimacs)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without Python optimization to keep assertions active.')
    main()
