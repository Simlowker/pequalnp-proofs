# Projecting the same circuit to the high input

The first Lean file converts a hypothetical circuit for L-meta-3971 into a straight-line program on 512-bit truth columns. The second file proves that, after setting t to one, at least one of the twelve ordinary AND/OR instructions in that program has a constant operand and can be dropped. The projection of the same program thus computes the high slice with at most eleven binary instructions and at most one NOT. The high slice is the six-cycle edge function together with two singleton inputs joined by OR.

To recheck, use the pinned Lean project and Mathlib build described in the parent directory. From the checkout's lean directory, set COFACTOR to the absolute path to this folder and run the following commands with a writable output directory.

```sh
lake env lean -R "$COFACTOR" -o "$COFACTOR/PetersenSingleInverterSearch.olean" "$COFACTOR/PetersenSingleInverterSearch.lean"
lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean -R "$1" "$1/PetersenHighCofactor.lean"' sh "$COFACTOR"
```
