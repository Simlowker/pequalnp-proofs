"""Verify the minimum of 15 gates for one-inverter formulas in Petersen task 3971.

Run with Python 3 and one-inverter3971.json in the same directory. Only the
standard library is needed. The certificate applies to formulas (trees).
"""
import json
from pathlib import Path

EDGES = [(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4),(0,8),(3,8)]
def graph(mask):
    return any((mask>>i)&(mask>>j)&1 for i,j in EDGES)
def inputs(mask):
    raw=[mask>>i&1 for i in range(9)]
    return raw+[raw[1]|raw[8],0,1]
def check(condition, message):
    if not condition:
        raise ValueError(message)
def capacity(matrix, rows, cols, threshold):
    # Check an upper bound on every all-selected subrectangle. For fixed
    # rows, the best columns are exactly those whose signed sum is positive.
    if not rows or not cols:
        return 0 <= threshold
    a=[[matrix[i][j] for j in cols] for i in rows]
    if sum(max(0,w) for row in a for w in row)<=threshold:
        return True
    if len(a)>len(a[0]):
        a=list(zip(*a))
    totals=[0]*len(a[0])
    previous=0
    if threshold<0:
        return False
    for i in range(1,1<<len(a)):
        gray=i^(i>>1)
        change=gray^previous
        index=change.bit_length()-1
        sign=1 if gray&change else -1
        totals=[t+sign*z for t,z in zip(totals,a[index])]
        if sum(t for t in totals if t>0)>threshold:
            return False
        previous=gray
    return True
def main():
    data=json.loads(Path(__file__).with_name('one-inverter3971.json').read_text())
    P,N=data['rows'],data['cols']
    check(len(set(P+N))==len(P)+len(N),'duplicate test')
    check(all(0<=r<512 and graph(r) for r in P),'positive label')
    check(all(0<=r<512 and not graph(r) for r in N),'negative label')
    # Each ordinary input has a rising pair on which all other inputs are
    # fixed. A monotone outer formula with a single negative subtree needs
    # all nine ordinary literals outside that subtree: its value rises but
    # the complemented subtree can only fall. Thus under a 14-leaf budget
    # the negated monotone subtree has at most 5 leaves.
    for i in range(9):
        check(any(not (r>>i&1) and not graph(r) and graph(r|1<<i)
                  and all(inputs(r)[j]==inputs(r|1<<i)[j] for j in range(12) if j!=i)
                  for r in range(512)),f'missing positive occurrence witness for input {i}')
    coeffs=[]
    for number,cert in enumerate(data['certificates']):
        w,D=cert['w'],cert['d']
        check(isinstance(D,int) and D>0 and len(w)==len(P) and all(len(a)==len(N) and all(isinstance(x,int) for x in a) for a in w),'matrix shape')
        for i in range(12):
            R=[j for j,r in enumerate(P) if inputs(r)[i]]
            C=[j for j,r in enumerate(N) if not inputs(r)[i]]
            check(capacity(w,R,C,D),f'positive literal cap in matrix {number}')
        coeffs.append((w,D,sum(map(sum,w))))
    # A monotone formula partitions the positive x negative matrix into
    # rectangles, one per leaf. At an OR, partition rows by a true child;
    # at an AND, partition columns by a false child. The other side stays
    # intact. Every leaf rectangle is contained in its separator R x C.
    check(any(total>14*D for w,D,total in coeffs),'lower bound with no NOT')
    rows=P+N
    layers=[set(),{sum(inputs(r)[i]<<j for j,r in enumerate(rows)) for i in range(12)}]
    seen=set(layers[1])
    for k in range(2,6):
        current=set()
        for a in range(1,k//2+1):
            for x in layers[a]:
                for y in layers[k-a]:
                    current.add(x&y)
                    current.add(x|y)
        current-=seen
        layers.append(current)
        seen|=current
    # Minimum costs suffice: replacing either child by a smaller expression
    # with the same sampled column preserves the parent column on these rows.
    for k in range(1,6):
        ids=data['assignment'][k]
        check(len(ids)==len(layers[k]),'missing inner columns')
        for H,ci in zip(sorted(layers[k]),ids):
            check(0<=ci<len(coeffs),'matrix index')
            w,D,total=coeffs[ci]
            R=[j for j in range(len(P)) if not (H>>j&1)]
            C=[j for j in range(len(N)) if H>>(len(P)+j)&1]
            # Besides the single NOT-H leaf, at most 14-k leaves of the
            # outer formula remain. Their total capacity is (14-k)*D.
            check(capacity(w,R,C,total-(14-k)*D-1),f'insufficient certificate for {k}, {H}')
    # The explicit upper bound uses 16 leaves and therefore 15 binary gates.
    def formula(m):
        a=inputs(m)
        return ((a[0] and (a[4] or a[9])) or
                (a[1] and (a[2] or a[5])) or
                ((a[2] or a[7] or a[8]) and a[3]) or
                ((a[2] or a[4]) and a[6]) or ((a[4] or a[5]) and a[7]))
    check(all(formula(r)==graph(r) for r in range(512)),'upper bound')
    # With no inverter, 14 gates permit 15 leaves. A matrix exceeding
    # 15*D is needed for this case. With one inverter only 14 leaves fit.
    check(any(total>15*D for _,D,total in coeffs),'15-leaf monotone case')
    print(f'Verified {len(coeffs)} matrices, {sum(map(len,layers))} inner columns and 512 upper-bound rows. Minimum: 15 gates for formulas with at most one NOT.')
if __name__=='__main__':
    main()
