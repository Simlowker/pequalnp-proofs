"""Check a Petersen-graph lower bound with a reusable binary gate and inverter."""
import json
from itertools import combinations
from pathlib import Path
from verify_one_inverter3971 import graph, inputs, capacity, check

def configurations(rows):
    raw = [tuple(inputs(r)[i] for r in rows) for i in range(10)]
    def invert(x):
        return tuple(1-v for v in x)
    def binary(op,x,y):
        return tuple((a & b) if op == 'and' else (a | b) for a,b in zip(x,y))
    for a,b in combinations(range(10),2):
        for op in ('and','or'):
            s = binary(op,raw[a],raw[b])
            for h in range(10):
                yield f'{op}-{a}-{b}-neg-{h}', s, invert(raw[h])
            yield f'{op}-{a}-{b}-neg-result', s, invert(s)
    for h in range(10):
        z = invert(raw[h])
        for j in range(10):
            for op in ('and','or'):
                yield f'neg-{h}-{op}-{j}', z, binary(op,z,raw[j])

def main():
    data = json.loads(Path(__file__).with_name('two-gate.json').read_text())
    positive, negative = data['positive'], data['negative']
    rows = positive + negative
    check(len(set(rows)) == len(rows) and all(isinstance(r,int) and 0 <= r < 512 for r in rows), 'invalid rows')
    check(all(graph(r) for r in positive) and all(not graph(r) for r in negative), 'incorrect labels')
    raw = [tuple(inputs(r)[i] for r in rows) for i in range(12)]
    checked = set()
    def certify(i, column):
        if (i,column) in checked:
            return
        m = data['matrices'][i]
        pos = [j for j in range(len(positive)) if column[j]]
        neg = [j for j in range(len(negative)) if not column[len(positive)+j]]
        check(capacity(m['w'],pos,neg,m['d']), 'rectangle capacity')
        checked.add((i,column))
    for i,m in enumerate(data['matrices']):
        w,d = m['w'],m['d']
        check(type(d) is int and d > 0 and len(w)==len(positive) and
              all(len(r)==len(negative) and all(type(x) is int for x in r) for r in w), 'matrix shape')
        check(sum(map(sum,w))>13*d, 'insufficient matrix weight')
        for x in raw:
            certify(i,x)
    total = 0
    for name, a, b in configurations(rows):
        j=data['assignment'][name]
        check(type(j) is int and 0 <= j < len(data['matrices']), 'missing matrix')
        certify(j,a)
        certify(j,b)
        total += 1
    check(total==1190 and len(data['assignment'])==total,'configuration count')
    print(f'Checked all {total} two-gate configurations with {len(data["matrices"])} integer matrices. Every 12-gate residual tree disagrees with the target.')

if __name__=='__main__':
    main()
