# Read-one replacement for incidence circuits on a projective plane

For a projective plane of order `q ≥ 2`, put `N = q² + q + 1`. A circuit decides whether the selected points and lines include an incident pair. In a read-one circuit, each such minimal pair has a proof tree that reads each endpoint once. An arbitrary input can still feed several gates.

**The exact read-one minimum is `N(q+2) − 1`.** The star construction attains it. The project’s vertex-cover lower bound and a perfect matching give the reverse inequality. Consequently, an unrestricted AND/OR circuit `C` admits a read-one replacement of at most its size precisely when `C.size ≥ N(q+2) − 1`. This reduces L-meta-2583 to a numerical lower bound. The bound for all unrestricted circuits remains open.

## A test for a proposed smaller circuit

For each wire, follow OR gates backwards, stopping at any AND gate. Record the primary inputs reached. Mark an AND gate if one input from its first set and one from its second set form a pair which is not a graph edge. This includes a repeated vertex. Let `e` be the number of marked gates. Disable all marked gates at once by setting their outputs to false. Evaluate the circuit on each incident point-line pair with all other inputs false. Let `b` be the number of these pairs which the modified circuit fails to accept.

For every correct fan-in-two AND/OR circuit on the plane, `plane_loss` proves

```
N(q+2) + e ≤ C.size + 1 + b + floor(b/(q+1)).
```

`replacement_if` proves the requested read-one replacement whenever `b + floor(b/(q+1)) ≤ e`. In particular, a proposed circuit saving one gate, with exactly one marked AND, must lose at least two incidences when that gate is disabled. The test allows arbitrary sharing and arbitrary depth.

`intact_loss` removes the floor term whenever `b ≤ q+1` and each point and line retains at least one incidence. Its geometric ingredient, `surviving_matching`, proves that deleting at most `q+1` incidences preserves a perfect matching under that same condition. The threshold is sharp for isolating a vertex, since each point and each line has exactly `q+1` incidences.

The gate argument counts edges still accepted *after simultaneous deletion*. A gate can fire on a pair that remains accepted through another branch. The proof charges only pairs actually lost at the output. For arbitrary rectangle-free bipartite graphs, `bipartite_bound` bounds the number of surviving edges plus the size of a cover of those edges plus the number of marked gates by `C.size + 1`.

## Reproduce the checks

From the root of this checkout run the following commands with the pinned Lean 4.36.0 environment.

```sh
cd lean
lake build PEqualNP.Outside.L_meta_4767 PEqualNP.Outside.L_meta_4897 PEqualNP.Outside.L_meta_7684
lake env lean ../certificates/L-meta-2583/ProjectiveLoss.lean
```

`ProjectiveLoss.lean` reuses the gate accounting in L-meta-4767, the vertex-cover lower bound in L-meta-4897 and the star construction in L-meta-7684. Its formal results use the posted projective-plane axioms, including for planes given without coordinates.
