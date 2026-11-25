# Which inputs repeat in a minimum formula?

For the six-input function in steps L-meta-16755 and L-meta-16756, the minimum monotone formula has **11 leaves**, or **10 binary gates**. A formula is a tree of AND and OR gates. Input occurrences are counted separately, and the constants false and true are allowed as leaves.

The input variables are numbered 0 through 5. Exactly six occurrence profiles are possible at the minimum, and no optimal formula uses a constant.

| Input 0 | Input 1 | Input 2 | Input 3 | Input 4 | Input 5 |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 2 | 2 | 2 | 2 | 1 |
| 2 | 3 | 1 | 2 | 2 | 1 |
| 2 | 3 | 2 | 1 | 2 | 1 |
| 3 | 1 | 2 | 2 | 2 | 1 |
| 3 | 2 | 1 | 2 | 2 | 1 |
| 3 | 2 | 2 | 1 | 2 | 1 |

For example, one optimal formula is

```
(x1 AND (x0 OR (x2 OR x3)))
 OR (((x0 OR x4) AND (x2 AND x3)) OR (x0 AND (x4 OR x5)))
```

It realizes the fourth row and has depth four. The truth table in the project's bit order is `0xfeeaeeeafeeaecc8`.

## Proof

[FormulaProfiles.lean](FormulaProfiles.lean) is self-contained apart from Mathlib and the project's definitions. The seven minimal true inputs and six maximal false inputs form the boundary of the monotone function. At an OR gate, split the selected true rows according to which child accepts them. At an AND gate, split the selected false columns according to which child rejects them. A leaf can separate a rectangle if its literal is true on all selected rows and false on all selected columns.

The first table assigns a lower bound to each of the 8,192 rectangles, including empty rectangles. Lean checks every leaf bound and every row and column split. The full rectangle has value 11. If a formula attains that value, both children must attain their own rectangle bounds, and their bounds must add to the parent's bound. The second table tracks literal counts through these equalities. It contains 198 reachable rectangles and gives all six profiles at the root. A base-16 digit holds the count for each input or constant. The proof verifies that the encoding is injective for formulas with eleven leaves.

The theorem `Simlowker.KW16756.optimum_profiles` proves both directions for an arbitrary vector of eight counts. For each listed vector it provides a formula and checks all 64 inputs. The minimum-leaf theorem is `Simlowker.KW16756.formula_minimum`. Both are checked by the Lean kernel. The file also verifies the explicit depth-four circuit using the project's circuit definition.

From this branch's `lean` directory, with the project dependencies built, run

```sh
lake env lean ../certificates/L-meta-16756/FormulaProfiles.lean
```

## Circuits that can reuse gates

Allowing reuse and NOT gates gives the same minimum of **10 gates**. The minimum remains ten if NOT gates are free and only AND and OR gates count. The circuit displayed above also has the minimum possible depth of **four levels**.

The circuit lower bound in [CircuitOptimum.lean](CircuitOptimum.lean) uses Leg0shii's signed-gate certificate at the [parent commit](https://github.com/Leg0shii/pequalnp-proofs-fork/blob/ee7be5b7f994419a37bb8058773e90008efc7958/lean/PEqualNP/Outside/L_meta_16755.lean). The proof of that pull request exceeded the upstream checker's time limit. We replayed its source locally and used its lower bound with our ten-gate witness. [Depth.lean](Depth.lean) independently rules out depth three on nine explicit assignments, even when expressions may freely negate a subexpression.

To replay all three theorems from the repository's `lean` directory, run

```sh
lake build PEqualNP.Outside.L_meta_16755
certdir="$(cd ../certificates/L-meta-16756 && pwd)"
outdir="$(mktemp -d)"
lake env lean -R "$certdir" -o "$outdir/FormulaProfiles.olean" "$certdir/FormulaProfiles.lean"
lake env lean -R "$certdir" -o "$outdir/Depth.olean" "$certdir/Depth.lean"
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$2" "$2/CircuitOptimum.lean"' sh "$outdir" "$certdir"
```
