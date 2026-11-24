"""Verify the lower bound when the inverter may have arbitrary fan-out."""
import json
from pathlib import Path
import verify_one_inverter3971 as tree

def main():
    tree.main()
    root = Path(__file__).resolve().parent
    base = json.loads((root / 'one-inverter3971.json').read_text())
    extra = json.loads((root / 'shared-inverter.json').read_text())
    positive, negative = base['rows'], base['cols']
    matrices = base['certificates'] + extra['additional_matrices']
    for matrix in extra['additional_matrices']:
        w, d = matrix['w'], matrix['d']
        tree.check(isinstance(d, int) and d > 0 and len(w) == len(positive) and
                   all(len(row) == len(negative) and all(isinstance(v, int) for v in row) for row in w), 'matrix dimensions')
        for j in range(12):
            rows = [i for i, r in enumerate(positive) if tree.inputs(r)[j]]
            cols = [i for i, r in enumerate(negative) if not tree.inputs(r)[j]]
            tree.check(tree.capacity(w, rows, cols, d), 'ordinary literal capacity')
    points = positive + negative
    layers = [set(), {sum(tree.inputs(r)[j] << i for i, r in enumerate(points)) for j in range(12)}]
    seen = set(layers[1])
    for k in range(2, 5):
        words = set()
        for a in range(1, k // 2 + 1):
            for x in layers[a]:
                for y in layers[k-a]:
                    words.update((x & y, x | y))
        words -= seen
        seen |= words
        layers.append(words)
    total_checks = 0
    for fan in range(2, 6):
        for k in range(1, 7 - fan):
            indices = extra['assignment'][f'{fan}/{k}']
            tree.check(len(indices) == len(layers[k]), 'missing word')
            for h, j in zip(sorted(layers[k]), indices):
                tree.check(isinstance(j, int) and 0 <= j < len(matrices), 'bad matrix index')
                mat = matrices[j]
                w, d = mat['w'], mat['d']
                rows = [i for i in range(len(positive)) if not (h >> i & 1)]
                cols = [i for i in range(len(negative)) if h >> (len(positive) + i) & 1]
                cap = (sum(map(sum, w)) - (15-k-fan)*d - 1) // fan
                tree.check(tree.capacity(w, rows, cols, cap), f'failed for fan-out {fan}, inner cost {k}, column {h}')
                total_checks += 1
    print(f'Verified {total_checks} shared-inverter cases using {len(matrices)} matrices. Any 14-gate counterexample must reuse an AND or OR gate.')

if __name__ == '__main__':
    main()
