# Residual edges of least top-form circuits

This certificate gives partial upper bounds toward desk step L-meta-1735. Let $s$ be the number of gates in a least, exact binary AND/OR circuit in top form for the graph-edge function. Let $U$ be the set of edges left after removing the pairs covered by opposite literal sides of a clean top AND. Assume the graph has girth at least five.

* If the circuit has $t$ dirty AND gates, then $|U| ≤ 4^t(s+1)$.
* Let $q$ count the supported vertices whose signature occurs exactly once on the support. Then $|U| ≤ 2(s+1)+q^2$.
* Since $q ≤ 4^t$, we also obtain $|U| ≤ 2(s+1)+16^t$. For instance, $q^2 ≤ s+1$ gives $|U| ≤ 3(s+1)$, even when the number of dirty AND gates grows.

The Lean statement for these three bounds is `Simlowker.Types1735.girth_bounds` in [TypeBounds.lean](TypeBounds.lean). The requested uniform linear estimate for unrestricted circuits remains open.

## Matching bounds

Write $t$ for the number of dirty AND gates. The following results also count the residual edges when the number of dirty gates grows.

* Every induced matching of residual edges has at most $2t$ edges. Here induced refers to the original graph, so extra edges between matching endpoints are forbidden even when those edges lie outside the residual set.
* The residual edges admit a vertex cover of size at most $256t^2$. Every residual edge has an endpoint in this cover.
* The edge count satisfies both $|U| ≤ 4ts$ and $|U| ≤ s+1+65536t^4$. In particular, $65536t^4 ≤ s+1$ implies $|U| ≤ 2(s+1)$.

[LocalWitnesses.lean](LocalWitnesses.lean) proves the induced-matching bound. Each residual edge has an orientation with the following property. If an independent vertex set contains its first endpoint, some dirty operand in the accepting top’s cone contains its other endpoint among its literal inputs and misses the entire independent set. For each edge of an induced matching, take its first endpoint together with the second endpoints of all the other edges. This set is independent. The resulting dirty operand distinguishes that edge from every other edge of the matching, so the matching uses distinct operand slots.

[MatchingBounds.lean](MatchingBounds.lean) proves the vertex-cover and edge-count bounds. In an ordinary matching, two edges conflict when the original graph has an edge between their endpoints. An independent set of this conflict graph is an induced matching. Turán’s theorem applied to the complement bounds how sparse the conflict graph can be. On the other hand, the girth bound limits the number of original edges among the matching endpoints. Together these inequalities bound an ordinary matching by $128t^2$. The endpoints of any maximal ordinary matching give the claimed vertex cover. Counting neighbors in that cover gives the fourth-power remainder.

## Why signatures control residual edges

An AND gate is dirty if it accepts an assignment that contains no graph edge. A vertex signature records whether its input wire reaches each of the two operands of each dirty AND through OR gates alone. There are at most $4^t$ such signatures.

In top form, every AND reached by following an operand of an AND down through OR gates is dirty. Induction in gate order therefore shows that replacing one endpoint of a pair by any vertex with its signature preserves the values of all dirty gates. For every residual edge, some clean top accepts the assignment enabling just its two endpoints. Since the edge lies outside the cross pairs of the clean tops, one endpoint can be replaced throughout its signature class while preserving acceptance by that top. The other endpoint is consequently adjacent to the entire class.

Two distinct vertices have at most one common neighbor in a graph without four-cycles. Every class containing at least two vertices therefore has at most one vertex adjacent to all its members. Summing over such classes costs at most the support size. For the $q$ singleton classes, count the incidences from a supported vertex to singleton neighbors. Fix one singleton neighbor for each vertex that has one. Each extra incidence gives an ordered pair consisting of the fixed singleton neighbor and the extra singleton neighbor. The starting vertex is adjacent to both. Each ordered pair has at most one such common neighbor. This gives the second bound.

## Other checked statements

[WideGates.lean](WideGates.lean) proves that if more than four vertices individually certify that a gate's acceptance forces a graph edge when their input is present, all independent accepting witnesses of size at most two share a vertex, provided any such witness exists. At a wide AND, every accepting pair either intersects a fixed set of at most two vertices or enables an earlier AND that reaches one operand through OR wires.

[DegreeBounds.lean](DegreeBounds.lean) proves $(2|U|)^2 ≤ (s+1)^2s$ from the girth and optimality hypotheses alone. It also gives a peeling result for any degree threshold $d$. If $|U| > 2d(s+1)$, some residual subgraph has more than $d(s+1)$ edges and every nonisolated vertex has degree at least $d+1$.

## Replaying the certificate

The parent project revision is `3a6fb91512ff77bffc0a5b66c481b3e63df67fa2`. The certificate imports the project's definitions and two merged proofs, L-meta-1506 for circuit evaluation through OR wires and L-meta-2074 for the support bound. Use the checkout's pinned Lean toolchain and Mathlib dependencies. From the repository root:

```sh
cd lean
lake build +PEqualNP.Outside.L_meta_1506 +PEqualNP.Outside.L_meta_2074
lake env sh -eu -c '
  src=../certificates/L-meta-1735
  cache=$(mktemp -d)
  export LEAN_PATH="$cache:$LEAN_PATH"
  for module in WideGates DegreeBounds TypeBounds LocalWitnesses MatchingBounds; do
    lean -R "$src" -o "$cache/$module.olean" "$src/$module.lean"
  done
'
```

Each file prints the axioms for its main results. The printed list for `girth_bounds` and `quartic_remainder` contains `propext`, `Classical.choice`, and `Quot.sound`.
