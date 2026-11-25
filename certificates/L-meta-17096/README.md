# Exact circuit and formula sizes for the three-sun graph

The six inputs indicate which graph vertices are selected. The function is true when the selection contains both endpoints of at least one of the nine edges 01, 02, 12, 13, 23, 04, 24, 05, 15. In the project's bit order, its truth table is `0xfefefeeefefafce8`.

| Model | Minimum binary gates |
| --- | ---: |
| Circuits with fan-in at most two, reuse allowed, NOT gates free | 9 |
| Formulas with binary AND and OR, NOT gates free | 10 |

Both upper bounds use only positive inputs, AND and OR. A circuit can therefore save exactly one gate by reusing intermediate results, even if a formula can negate any subexpression for free. When NOT gates count towards circuit size, the minimum remains nine and every minimum-size circuit has no NOT gate.

## Proof and attribution

[ExactSize.lean](ExactSize.lean) supplies a nine-gate AND/OR circuit and an eleven-leaf AND/OR formula. Lean checks each witness on all 64 inputs. The circuit lower bound is Leg0shii's signed live-wire certificate from [PR 21357](https://github.com/open-goat/pequalnp-proofs/pull/21357), included unchanged in the parent commit. Separate nine-gate upper bounds appear in [PR 21403](https://github.com/open-goat/pequalnp-proofs/pull/21403), [PR 21638](https://github.com/open-goat/pequalnp-proofs/pull/21638) and [PR 21665](https://github.com/open-goat/pequalnp-proofs/pull/21665).

The formula lower bound uses a matrix of integer weights on true and false inputs. Its total weight is 21. For every signed input literal, each rectangle it separates has weight at most two. Splitting a formula at an AND gate partitions the false inputs, and splitting at an OR gate partitions the true inputs. Induction gives at least eleven leaves, hence at least ten binary gates. Pushing arbitrary negations to the literals preserves both the Boolean function and the number of binary gates.

From the repository's `lean` directory in this branch, run

```sh
lake build PEqualNP.Outside.L_meta_17095
lake env lean ../certificates/L-meta-17096/ExactSize.lean
```

The exact optima are `Simlowker.ThreeSun.free_negation_circuit_optimum` and `Simlowker.ThreeSun.FormulaBound.free_negation_tree_optimum`.
