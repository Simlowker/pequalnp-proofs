# Seventeen minimum circuits for a six-input function

For truth table `0xeac8e0c0eac0e0c0`, the minimum is seven gates, and the minimum depth is four. One circuit attains both minima. The four minimal true input masks are 6, 13, 25 and 51, with input 0 as the least significant bit.

Every minimum circuit in the project's fan-in-two AND/OR/NOT model uses only AND and OR. The seven-binary-gate lower bound comes from [NotoriousH2's L-meta-12981 proof](https://github.com/open-goat/pequalnp-proofs/pull/16792). [Hemmurs's independent proof](https://github.com/open-goat/pequalnp-proofs/pull/16821) already exhibits a seven-gate upper bound. This branch builds on NotoriousH2's commit and supplies a depth-four witness, a depth lower bound, and a classification.

## What the counts mean

The inputs have fixed names. A normalized program ends in the output and each gate reads two distinct, earlier wires. Canonical forms identify programs under reordering the two inputs of any gate and renumbering gates in topological order. Associativity and input relabeling do not identify forms.

There are 280 normalized programs, representing **17 distinct circuits**. Every one has four AND gates and three OR gates. Nine are formulas, meaning that every intermediate result has one consumer. The other eight reuse exactly one intermediate. Three of the 17 circuits have depth four, nine have depth five, and five have depth six.

| Intermediate reused | Number of circuits |
| --- | ---: |
| `x0 & x3` | 4 |
| `((x1 & x5) &#124; x3) & x0` | 2 |
| `(x2 &#124; x4) & x0` | 1 |
| `(x3 &#124; x5) & x0` | 1 |

A simple depth-four formula is `(x1 & x2) | (((x1 & x5) | x3) & (x0 & (x2 | x4)))`.

## Lean theorems

From the repository's `lean/` directory, use the pinned Lean toolchain and Mathlib dependencies.

```sh
lake build PEqualNP.Outside.L_meta_12981 Mathlib
lake env lean ../certificates/L-meta-12982/OptimalCircuits.lean
```

* `Optimal12982.exact_size`, `optimum_is_monotone`, `balanced`, and `computes` use the project's actual circuit semantics, including default reads and gates of smaller arity.
* `Formulas12982.all_minimum_trees` proves that any AND/OR formula with at most eight leaves computing the table has eight leaves and a canonical code in a list of nine. `all_attained` verifies nine distinct representatives on all 64 assignments. The proof propagates nine-bit evaluation signatures and possible canonical codes through every tree split of the relevant leaf budgets.
* `Depth12982.at_least_four` shows that even with arbitrary formula size, free constants and free negations, binary depth is at least four. Nine sampled assignments suffice. The proof checks closure of the signed wire signatures through three levels. `circuit_depth_at_least_four` transfers this bound to the project's circuit depth by unfolding arbitrary legal circuits, including shared wires. Each theorem above is in the `Simlowker` namespace. The source prints its axiom audits.

## Reproduce the full circuit classification

Run the following from this directory. The Python checker uses the standard library. The LRAT replay uses `zstd` and [lrat-trim](https://github.com/arminbiere/lrat-trim/tree/423194927df747528d5b7364806b5b77b2660c12).

```sh
python3 verify_catalogue.py
zstd -dc exhausted.lrat.zst | lrat-trim --no-trim --rup exhausted.cnf -
```

The first command checks every circuit against all 64 rows and reconstructs the DIMACS file byte for byte. The second prints `s VERIFIED` and exits with status 20 on success. It checks an empty clause derived after 64,498 RUP additions.

The CNF chooses an operation and two ordered source indices per gate, then imposes gate semantics on the four minimal true and five maximal false input rows. The code verifies that the target is monotone. Consequently, matching the nine boundary rows determines the full table for every monotone circuit. Each catalogue entry blocks exactly its operation and wiring choices. Refuting the remaining CNF proves exhaustion, independently of how the catalogue was found.

For each of the 280 programs the checker also verifies that all wires compute distinct functions and every intermediate is used. Equal subexpressions in the expanded canonical expression therefore identify exactly the same intermediate wire. This makes that expression a complete identifier for these DAGs under the stated equivalence. The checker independently compares the typed graph edges labeled by their 64-bit wire functions and verifies that both methods give the same partition.
