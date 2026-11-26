# A tree-size lower bound for PHP(5,4) in Res(⊕)

Every tree refutation of the five-pigeon, four-hole formula uses at least **67 axiom leaves** and **133 line occurrences**. In a tree, each use of a previous derivation copies the derivation. The project's L-pcx-179 instead asks for a *list* of at most 123 lines, where a line can be reused. Such a list would have at least ten more occurrences in its expansion to a tree than it has entries. Its existence remains open in this experiment.

## Replay

Run `python3 -I verify.py` in this directory with Python 3.10 or later. The checker has no external dependencies and uses exact integers. It reads [weights.json](weights.json), checks its witnesses against the 45 distinct PHP axioms, and enumerates all 1,048,575 nonzero linear queries on the 20 variables.

[Tree179.lean](Tree179.lean) verifies the structural part against Lean 4.36.0 and the project's inference rules. In particular, `Simlowker.Pigeon179.TreeBounds.expansion` takes the numerical root-cover bound `RootBudget 67` as an explicit hypothesis. The Python verifier establishes the finite bound separately. The combined result therefore has a computer-assisted proof with a Python verification step. To replay the structural lemma in a project checkout at the pinned revision, run `lake build PEqualNP.Defs` under `lean/`, then `lake env lean /absolute/path/to/Tree179.lean` in the same directory. The theorem's axiom report lists `propext`, `Classical.choice`, and `Quot.sound`.

## Why the root gives a size bound

A falsifying assignment for any derived clause falsifies an axiom in the subtree deriving it. For a weakening this follows from the contrapositive of its stated implication. For a resolution, a falsified resolvent forces one parent to be false, according to the value of the pivot parity.

Starting with a universally false conclusion, pass through any final weakenings. A resolution on the empty variable set has constant parity and one parent is again universally false. A PHP axiom is satisfiable. Consequently, some resolution on a nonempty linear query splits the assignment cube in two. Each child needs enough axiom leaves to cover its half of the cube. A cover consists of axioms whose falsifying sets together contain all assignments in that half.

For 1,048,320 queries, use 360 assignments that violate exactly one axiom each. Each of the five pigeon axioms has 24 such witnesses in the sample and each of the forty collision axioms has six. Every axiom must occur on at least one side. For each of these queries at least 22 axioms have a witness on *both* sides. The two children therefore need at least 45 + 22 leaves in total.

The other 255 queries select an XOR of whole rows and whole columns. The verifier checks this classification by comparing sets of exact 20-bit masks. Permuting pigeons and holes maps each query to one of 14 representatives while preserving the PHP axioms. Complementing both selected index sets leaves the XOR mask unchanged, so at most two of the five rows need be selected in each representative.

For each representative and each side, the certificate identifies compulsory axioms using single-fault witnesses. It then assigns integer weights to additional assignments outside the compulsory axioms. If every eligible axiom covers weight at most D and the total weight is S, then covering those assignments costs at least the ceiling of S/D additional axioms. A binary split can further distinguish covers that contain a chosen axiom from covers that omit it. Both possibilities are checked. Summing the two side bounds gives at least 67 for every representative.

A tree with unary weakenings and binary resolutions has at least twice its number of leaves minus one nodes. This gives the stated 133.

## Project sources

The variable indexing in the verifier is `4*pigeon + hole`. The first five axioms require each pigeon to occupy a hole. The remaining forty prohibit two distinct pigeons from occupying the same hole. The project represents a linear clause as a disjunction of parity equations. [PHP definition](https://github.com/open-goat/pequalnp-proofs/blob/3a6fb91512ff77bffc0a5b66c481b3e63df67fa2/lean/PEqualNP/Defs/ProofComplexity.lean#L65-L73) · [Res(⊕) rules](https://github.com/open-goat/pequalnp-proofs/blob/3a6fb91512ff77bffc0a5b66c481b3e63df67fa2/lean/PEqualNP/Defs/ProofComplexityLin.lean#L24-L58).
