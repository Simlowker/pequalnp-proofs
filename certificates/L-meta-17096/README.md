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

## Depth and the optimal circuits

Counting each gate, including NOT, as one gate gives an exact size–depth tradeoff. Nine gates can achieve depth five. Ten gates suffice to achieve depth four. Depth three is impossible at any size. The Lean proof unfolds any circuit into an expression, preserving its evaluation. A binary expression of depth three has at most eight leaves, while the formula bound above requires eleven.

The catalogue contains six size-nine circuits when input labels are fixed and gate ordering and operand ordering are ignored. Three have depth five and three have depth six. The symmetries of the graph identify the three choices at each depth. Every circuit uses three AND gates and six OR gates and reuses precisely two intermediate results. No size-nine circuit achieves depth four.

For example, set `A = x0 OR x3`, `B = x1 OR x4`, `U = A OR B`, and `H = ((A AND B) OR x5) AND (x0 OR x1)`. The depth-five form computes `H OR (x2 AND U)`. The depth-six form computes `(H OR x2) AND U`. They agree because H implies U. Permuting the three central vertices and their corresponding outer vertices gives the other four labelled circuits.

**Checking completeness.** A minimum-size circuit has no NOT gate by the Lean theorem `optimal_no_not`. Dead gates can be deleted. Missing wires supply false. Constants, unary gates and repeated operands simplify by the identities for AND and OR. Any resulting smaller circuit would contradict the certified size lower bound. Thus a minimum circuit has nine live binary gates, each reading two distinct earlier wires. In each topological numbering, putting the smaller operand first is harmless. To obtain the numbering used by the checker, repeatedly choose the available gate with lexicographically smallest pair (larger operand, smaller operand). Any newly available gate must read the just-created wire, so its larger operand exceeds both operands of the chosen gate. Ties remain allowed. The output is last because all gates are live.

The CNF fixes the function on the minimal true and maximal false inputs. These suffice for monotone circuits. The checker verifies every listed program on all 64 inputs. It then adds one blocking clause for each of the 12 listed normalized programs and regenerates the CNF. The CNF chooses a representative under input relabelling by maximizing the characteristic vector of gates that read only primary inputs. Every orbit has such a representative, and the checker verifies that the catalogue is closed under all six automorphisms of the target. Checking the LRAT refutation certifies that the blocked CNF has no further models. The grouping into six circuits and two symmetry classes is checked in Python. The finite catalogue uses LRAT and the Lean depth bound uses the Lean kernel.

From this directory, with Python 3, zstd, and lrat-trim installed, run

```sh
python3 verify_catalogue.py /tmp/three-sun.cnf
zstd -d -c catalogue.lrat.zst > /tmp/three-sun.lrat
lrat-trim /tmp/three-sun.cnf /tmp/three-sun.lrat
```

The final checker prints `s VERIFIED`.
