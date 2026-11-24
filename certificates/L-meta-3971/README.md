# Petersen circuit bound, L-meta-3971

This archive checks the first premise of the submitted reduction on a computer
with Lean 4.36.0. It also includes both child statements and the reduction source.

The theorem `PetersenNegated3971.solved_tree_child` states that every allowed
circuit whose unfolded output uses at most one inverter and whose sum of
leaf occurrences and inverter occurrences is at most 15 disagrees with the
specified function on some input below 512. For a tree with unary NOT and
binary AND/OR, this sum equals the gate count plus one. The other child
covers shared circuits whose output has a larger unfolding. That case is open.

## Rebuild

1. Check out https://github.com/open-goat/pequalnp-proofs at commit
   `21afa4abc0b2f88d40b39b9eebd4aa4d799adb9e` and install its pinned Lean toolchain with elan.
2. In the checkout's `lean` directory, fetch the Mathlib cache with
   `lake exe cache get` and build the project definitions with `lake build PEqualNP.Defs`.
3. Extract this archive into an empty directory and run
   `python3 verify.py /absolute/path/to/pequalnp-proofs/lean`.

The script builds 118 proof modules in dependency order into a fresh temporary
directory, then Lean prints the axioms of the final theorem. The signed-matrix
computations use Lean kernel reduction. Allow several gigabytes of memory
and tens of minutes to rebuild. Python only invokes the compiler.
