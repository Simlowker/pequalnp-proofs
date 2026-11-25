"""Reconstruct the certified CNF and check every listed program on all inputs."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
TARGET = 0xFEFEFEEEFEFAFCE8
INPUTS = 6
OUTPUT = 14


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



def verify(destination):
    programs = json.loads((ROOT / 'programs.json').read_text())
    assert len(programs) == len({tuple(map(tuple, p)) for p in programs}) == 12
    e = Encoding()
    e.add_circuit_constraints(frontier())
    # Choose the smallest available (larger operand, smaller operand) pair first.
    # A gate becoming ready after this choice uses the new wire. Its larger operand
    # is therefore strictly greater than the previous pair's larger operand.
    for j in range(INPUTS, OUTPUT):
        for a in range(j):
            for b in range(a):
                e.clauses.append([-e.variable('src', j, 1, a), -e.variable('src', j+1, 1, b)])
            for u in range(a):
                for v in range(u):
                    e.clauses.append([-e.variable('src', j, 1, a), -e.variable('src', j+1, 1, a),
                                      -e.variable('src', j, 0, u), -e.variable('src', j+1, 0, v)])
    for i in range(INPUTS, OUTPUT):
        e.clauses.append([e.variable('src', j, k, i)
                          for j in range(i+1, OUTPUT+1) for k in range(2)])
    forms = {}
    for program in programs:
        key,edges,stats = classify(program)
        assert len(program) == 9
        assert [(b,a) for _,a,b in program] == sorted((b,a) for _,a,b in program)
        if key in forms:
            assert forms[key] == (edges,stats)
        forms[key] = (edges,stats)
        e.block(program)
        reads = Counter(a for _,left,right in program for a in (left,right))
        repeated = [i for i in range(INPUTS, OUTPUT) if reads[i] > 1]
        assert len(repeated) == 2
        assert all(reads[i] == 2 and program[i - INPUTS] in
                   [['|',0,3], ['|',1,4], ['|',2,5]] for i in repeated)
    assert len(forms) == 6
    assert Counter(d['depth'] for _,d in forms.values()) == {5:3, 6:3}
    assert all(d['ands']==3 and len(d['share'])==2 and d['leaf_reads']==12 for _,d in forms.values())
    from itertools import permutations
    automorphisms = [p for p in permutations(range(INPUTS))
                     if all((TARGET >> row & 1) == (TARGET >> sum(1 << p[i] for i in range(INPUTS)
                         if row >> i & 1) & 1) for row in range(1<<INPUTS))]
    def renamed(p, permutation):
        labels = list(map(str, permutation))
        for op,a,b in p:
            labels.append('(' + op.join(sorted([labels[a],labels[b]])) + ')')
        return labels[-1]
    orbits = {}
    for p in programs:
        key,_,stats = classify(p)
        orb = min(renamed(p,perm) for perm in automorphisms)
        orbits.setdefault(orb,set()).add((key,stats['depth']))
    assert sorted((len(v), sorted({d for _,d in v})) for v in orbits.values()) == [(3,[5]),(3,[6])]
    # Relabel vertices so the set of input-only gates is the lexicographically
    # greatest characteristic vector in its orbit. The target is invariant.
    assert all(renamed(p, perm) in forms for p in programs for perm in automorphisms)
    types = [(a,b,op) for b in range(INPUTS) for a in range(b) for op in ('&','|')]
    for a,b,op in types:
        choices = []
        for j in range(INPUTS, OUTPUT+1):
            tag = e.variable('input-gate', j, a, b, op)
            choices.append(tag)
            parts = [e.variable('src',j,0,a), e.variable('src',j,1,b),
                     e.variable('and',j) * (1 if op == '&' else -1)]
            e.clauses.extend([[-tag,t] for t in parts])
            e.clauses.append([tag] + [-t for t in parts])
        flag = e.variable('present',a,b,op)
        e.clauses.extend([[-tag,flag] for tag in choices])
        e.clauses.append([-flag]+choices)
    for number,perm in enumerate(automorphisms):
        prefix = e.variable('initial-prefix',number)
        e.clauses.append([prefix])
        for i,(a,b,op) in enumerate(types):
            x=e.variable('present',a,b,op)
            y=e.variable('present',*sorted((perm[a],perm[b])),op)
            next_prefix=e.variable('prefix',number,i)
            e.clauses.extend([[-prefix,x,-y], [-prefix,x,y,next_prefix],
                              [-prefix,-x,-y,next_prefix]])
            prefix=next_prefix
    destination.write_text(e.dimacs())
    print('12 ordered programs, 6 distinct labelled circuits, 2 orbits; depth counts 3 + 3.')

if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cnf', type=Path, help='Destination for the reconstructed exhausted CNF')
    verify(parser.parse_args().cnf)
