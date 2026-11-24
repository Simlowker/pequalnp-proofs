# A 14-gate counterexample must reuse an AND or OR gate

For the function and input encoding of L-meta-3971, even an inverter with arbitrary fan-out cannot bring the minimum below 15 gates if every AND and OR gate has at most one use in the live computation. A 15-gate tree attains the bound. A 14-gate circuit that reuses a binary gate remains an open possibility.

Run `python3 verify_shared_not.py` in the extracted directory. This independent certificate uses Python's standard library and integer arithmetic. The Lean proof in the separate archive establishes the tree case. The additional shared-inverter result here is checked in Python.

Prune gates outside the output computation and pad missing AND/OR inputs with neutral constants. Suppose the only reused gate is the single inverter. Its input is a monotone tree with h leaves. Treating the inverter output as an additional input leaves a monotone output tree with o leaves. A size bound of 14 gives h+o≤15 since the two binary trees cost h−1 and o−1 gates and the inverter costs one. These two trees have disjoint internal gates under the hypothesis, even if they use the same primary variable. If the inverter is used zero or one time, the existing tree certificate applies.

Let f≥2 be the number of occurrences of the inverter output in the outer tree. All nine raw variables must occur outside the inverter. Each has a rising input pair on which the other inputs stay fixed, while the complemented inner value can only decrease. Consequently o≥9+f and h+f≤6. This accounts for all fan-outs, including f>5, which are impossible because h≥1.

On 12 positive and 22 negative samples enumerate all monotone truth columns up to minimum leaf cost k≤6−f. A column of minimum cost k can come from any larger tree of h≥k leaves. In a signed rectangle partition for the outer tree, an ordinary leaf contributes at most D and each of the f exceptional leaves contributes at most K. The total capacity of the ordinary leaves is at most (15−k−f)D. For every possible pair of inner column and fan-out, the verifier checks a matrix of total weight strictly greater than (15−k−f)D+fK. The bound K applies separately to every rectangle for the complemented input, even when that input occurs repeatedly.

The files include the earlier unshared-tree certificate as a dependency. Its explicit 15-gate witness also supplies the upper bound for this larger circuit class.
