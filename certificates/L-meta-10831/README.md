# A nine-input edge function with minimum circuit size 15

The graph has edges 04, 15, 06, 16, 26, 07, 37, 47, 28, 38 and 58. An input assigns one bit to each vertex. The function returns true exactly when both endpoints of some edge have value one. Circuit size counts AND, OR and NOT gates with fan-in at most two, with free input wires.

HoshinoStarry authored the lower bound in [upstream PR 14995](https://github.com/open-goat/pequalnp-proofs/pull/14995). That PR also credits earlier work, including benoitrazet. At the time of this replay the upstream checker had timed out twice and closed the PR. Simlowker reproduced the lower bound locally and combined it with the explicit upper bound in [ExactMinimum10831.lean](ExactMinimum10831.lean). The resulting Lean theorem states that a circuit of size at most `t` exists exactly when `15 ≤ t`.

A circuit attaining the bound computes the OR of five terms. Here `+` means OR and juxtaposition means AND.

```text
x0(x4+x6+x7) + x1(x5+x6) + x2(x6+x8) + x7(x3+x4) + x8(x3+x5)
```

## Reproduce the exact result

Use the Lean toolchain pinned by the project. In a checkout of [open-goat/pequalnp-proofs](https://github.com/open-goat/pequalnp-proofs/tree/c5fe0f918c0bb79c1799969d44cf83a8f5f5db28), build `PEqualNP.Defs` from the `lean/` directory. Download [HoshinoStarry’s original source file](https://raw.githubusercontent.com/HoshinoStarry/pequalnp-proofs/f1aef8b2abfe52760a79d8971a1d6d7160cb7a7b/lean/PEqualNP/Outside/L_meta_10830.lean). Keep the files from this certificate directory together, then run

```sh
python3 replay_10830.py /path/to/L_meta_10830.lean /path/to/pequalnp-proofs/lean
```

The script checks the SHA-256 of the original source, retains its proof terms, and divides 128 arithmetic blocks into 73 independently compiled groups. Lean checks all groups and their composition in a temporary directory, then checks the explicit 15-gate circuit and prints the axioms of the three resulting theorems. Use `--workers 2` to reduce the number of concurrent compiler processes. The unsplit source also passed a separate local kernel check.

[GraphBudget10831.lean](GraphBudget10831.lean) records Simlowker’s separate restriction and formula arguments. Fixing vertex 3 to zero gives the eight-vertex instance of L-meta-8439 and an independent lower bound of 14 gates for arbitrary circuits. A weighted rectangle certificate proves that a monotone formula for this graph requires at least 16 leaves. The displayed circuit, viewed as a formula, attains that number. To check this additional file, first build the project's outside modules L_meta_3223, L_meta_6678 and L_meta_8439.
