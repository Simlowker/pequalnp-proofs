"""Integer verification when t enters through a single shared OR with a primary companion."""
import json
from pathlib import Path
import verify_shared_not as baseline
from verify_one_inverter3971 import graph, inputs, capacity, check

def row(r, companion):
    a=inputs(r)
    return tuple(a[:8]+[a[9],a[8]|a[companion]])

def main():
    baseline.main()
    data=json.loads(Path(__file__).with_name('reader.json').read_text())
    positives,negatives=data['positive'],data['negative']
    rows=positives+negatives
    check(len(set(rows))==len(rows) and all(0<=r<512 for r in rows),'row range')
    check(all(graph(r) for r in positives) and all(not graph(r) for r in negatives),'labels')
    pairs=0;count=0
    for j in range(12):
        cubes=[row(r,j) for r in range(512)]
        if j in (8,10):
            check(all(x[-1]==inputs(r)[8] for r,x in enumerate(cubes)),'copy of t')
            continue
        if j not in (0,2,5,7):
            seen={}
            for r,x in enumerate(cubes):
                if x in seen and graph(r)!=graph(seen[x]):break
                seen[x]=r
            else:raise ValueError('no conflicting equal-input pair')
            continue
        for b in range(10):
            negset={x for r,x in enumerate(cubes) if not graph(r) and x[b]==0}
            check(any(graph(r) and x[b]==1 and x[:b]+(0,)+x[b+1:] in negset for r,x in enumerate(cubes)),'missing isolated rising input')
        info=data['cases'][str(j)]; matrices=info['matrices']
        basis=[sum(cubes[r][b]<<t for t,r in enumerate(rows)) for b in range(10)]
        allbits=(1<<len(rows))-1
        def cap(w,s,k):
            yes=[a for a in range(len(positives)) if s>>a&1]
            no=[a for a in range(len(negatives)) if not(s>>(a+len(positives))&1)]
            return capacity(w,yes,no,k)
        for mat in matrices:
            w,d=mat['w'],mat['d']
            check(type(d) is int and d>0 and len(w)==len(positives) and all(len(r)==len(negatives) and all(type(x) is int for x in r) for r in w),'matrix dimensions')
            check(all(cap(w,s,d) for s in basis+[0,allbits]),'ordinary input cap')
        m=matrices[info['mon']]
        check(sum(map(sum,m['w']))>13*m['d'],'unused inverter')
        layers=[set(),set(basis+[0,allbits])];seen=set(layers[1])
        for k in (2,3):
            layer={z for a in range(1,k//2+1) for u in layers[a] for v in layers[k-a] for z in (u&v,u|v)}-seen
            seen|=layer;layers.append(layer)
        for f in (1,2,3):
            for k in range(1,5-f):
                ids=info['assignment'][f'{f}/{k}']
                check(len(ids)==len(layers[k]),'missing inverter columns')
                for s,i in zip(sorted(layers[k]),ids):
                    check(type(i) is int and 0<=i<len(matrices),'invalid matrix index')
                    m=matrices[i];w,d=m['w'],m['d']
                    K=(sum(map(sum,w))-(14-k-f)*d-1)//f
                    check(cap(w,s^allbits,K),'inverter cap')
                    count+=1
        pairs+=10
    print(f'Checked 12 primary or constant companion choices, {pairs} isolated increases and {count} inverter cases. An AND or OR gate other than the reader must be reused when its companion is primary.')
if __name__=='__main__':main()
