"""Reconstruct the certified CNF and check every listed program on all inputs."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
TARGET = 0xEAC8E0C0EAC0E0C0
INPUTS = 6
OUTPUT = 12


def frontier():
    true = {r for r in range(64) if TARGET >> r & 1}
    false = set(range(64)) - true
    assert all(a & b != a for a in true for b in false)
    minimal = sorted(a for a in true if not any(b != a and a & b == b for b in true))
    maximal = sorted(a for a in false if not any(b != a and a & b == a for b in false))
    return minimal + maximal


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

    def add_circuit_constraints(self, rows):
        var = self.variable
        clauses = self.clauses
        for i in range(INPUTS):
            for row in rows:
                wire = var('wire', i, row)
                clauses.append([wire if row & (1 << i) else -wire])
        for node in range(INPUTS, OUTPUT + 1):
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
            wire = var('wire', OUTPUT, row)
            clauses.append([wire if TARGET >> row & 1 else -wire])

    def block(self, gates):
        clause = []
        for node, (op, a, b) in enumerate(gates, INPUTS):
            op_var = self.variable('and', node)
            clause.extend([-op_var if op == '&' else op_var,
                           -self.variable('src', node, 0, a), -self.variable('src', node, 1, b)])
        self.clauses.append(clause)

    def dimacs(self):
        header = f'p cnf {len(self.variables)} {len(self.clauses)}\n'
        return header + ''.join(' '.join(map(str, clause)) + ' 0\n' for clause in self.clauses)


def classify(gates):
    assert len(gates) == OUTPUT + 1 - INPUTS
    functions = [sum(1 << row for row in range(64) if row & (1 << i)) for i in range(INPUTS)]
    expressions = [str(i) for i in range(INPUTS)]
    levels = [0] * INPUTS
    reads = Counter()
    labelled_edges = []
    for node, (operation, a, b) in enumerate(gates, INPUTS):
        assert 0 <= a < b < node and operation in ('&', '|')
        fa, fb = functions[a], functions[b]
        functions.append(fa & fb if operation == '&' else fa | fb)
        expressions.append('(' + operation.join(sorted([expressions[a], expressions[b]])) + ')')
        labelled_edges.append((functions[-1], operation, *sorted([fa, fb])))
        levels.append(1 + max(levels[a], levels[b]))
        reads.update([a, b])
    assert functions[-1] == TARGET
    assert all(reads[i] for i in range(INPUTS, OUTPUT))
    # Every wire has a unique truth table, so equal subtrees mean the same wire.
    # This makes the canonical commutative expression capture sharing as well.
    assert len(set(functions)) == len(functions)
    key = expressions[-1]
    return key, tuple(sorted(labelled_edges)), dict(depth=levels[-1], ands=sum(g[0] == '&' for g in gates),
                     leaf_reads=sum(c.isdigit() for c in key),
                     share=sorted(expressions[i] for i in range(INPUTS, OUTPUT) if reads[i] > 1))


def verify():
    data = json.loads((ROOT / 'circuits.json').read_text())
    models = data['models']
    assert len({tuple(map(tuple, program)) for program in models}) == len(models)
    encoding = Encoding()
    encoding.add_circuit_constraints(frontier())
    catalogue = {}
    topology = {}
    for i, gates in enumerate(models):
        key, edges, stats = classify(gates)
        assert topology.setdefault(key, edges) == edges
        entry = catalogue.setdefault(key, dict(first=i, orders=0, **stats))
        assert all(entry[field] == value for field, value in stats.items())
        entry['orders'] += 1
        encoding.block(gates)
    assert len(set(topology.values())) == len(catalogue)
    assert catalogue == data['canon']
    assert encoding.dimacs().encode('ascii') == (ROOT / 'exhausted.cnf').read_bytes()
    profiles = list(catalogue.values())
    print('Ordered programs:', len(models), 'DAGs:', len(profiles))
    print('Depths:', sorted(Counter(d['depth'] for d in profiles).items()))
    print('AND counts:', sorted(Counter(d['ands'] for d in profiles).items()))
    print('DAGs without sharing:', sum(not d['share'] for d in profiles))
    print('CNF matches. Check exhausted.lrat.zst against it for completeness.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without Python optimization so assertions are active.')
    verify()
