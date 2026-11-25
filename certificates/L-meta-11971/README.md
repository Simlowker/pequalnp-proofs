# Duplicating an essential circuit input costs exactly one gate

`TwinReduction.lean` proves that substituting `x ∧ y` or `x ∨ y` for an essential input increases the minimum number of gates by exactly one. This holds at every fixed upper bound on the number of NOT gates in the project's fan-in-two model. A sequence of `d` such substitutions increases the minimum by `d`. See `split_budget`, `saving_iff` and `expansion_budget` in the `Simlowker.Twins11971` namespace.

For the seven-vertex graph of L-meta-11970/11971, two nonadjacent vertices have the same neighbors. Merging them gives a five-vertex path with a sixth vertex adjacent to every vertex of the path. The Boolean function is true when the selected vertices contain an edge. Its unrestricted minimum circuit size is **10 gates on the six-vertex core and 11 gates on the original graph**. Monotone circuits attain both minima. More generally, `Graph.family_exact` gives an exact minimum of `10 + d` for every function obtained from the core by `d` essential-input splits, at every NOT budget.

The Lean proofs `Graph.exact_core` and `Graph.exact_posted` explicitly assume that the concrete formula `Graph.formula` is unsatisfiable. `Export.lean` writes that definition to DIMACS. Its 12,736 clauses exclude a nine-gate monotone circuit on the core. Leg0shii's bound of ten binary gates on the original graph excludes a ten-gate circuit containing any NOT gate. The direct ten-gate witness for the core appears as `Graph.ten`.

## Reproduce the Lean checks

Use the Lean version pinned by this checkout, 4.36.0. From the repository root run the following commands. Lake fetches the dependencies on the first run.

```sh
export CERT="$PWD/certificates/L-meta-11971"
cd lean
lake build PEqualNP.Outside.L_meta_9526 PEqualNP.Outside.L_meta_11970 PEqualNP.Library.LRAT.Link2
lake env sh -c 'export LEAN_PATH="$CERT:$LEAN_PATH"; lean -R "$CERT" -o "$CERT/TwinReduction.olean" "$CERT/TwinReduction.lean" && lean -R "$CERT" --run "$CERT/Export.lean" "$CERT/core.cnf"'
cd "$CERT"
shasum -a 256 core.cnf
```

Expected SHA-256 of the exact Lean export is `32c8489d4b05b5f933298a85f24e7acef3da4bc83541659aa5ed777a63120cc5`.

## Reproduce the independent UNSAT check

With CaDiCaL 2.1.2 and lrat-trim on PATH, run the following commands in the certificate directory. A proof generated with another solver seed can differ while certifying the same formula.

```sh
cadical -q --unsat --seed=2 --lrat --no-binary core.cnf core.lrat
lrat-trim --no-trim --rup core.cnf core.lrat
```

CaDiCaL returns 20 for UNSAT. The independent checker returns 20 and prints `s VERIFIED` upon deriving the empty clause. The locally retained dependency-trimmed LRAT proof contains 2,313,431 additions. Its Zstandard-compressed SHA-256 is `db3402b759cc4afa789b0262fc2132946471f6b4713c8a9bf99e97e4ba375d1a`. Two independent programs verified this trimmed proof, including [lrat-trim at the exact revision used](https://github.com/arminbiere/lrat-trim/tree/423194927df747528d5b7364806b5b77b2660c12).

This branch builds on the circuit restriction and wire remapping results of hilelyos, the project's LRAT encoding and soundness theorem, and the binary lower bound and monotone witness of Leg0shii. [Leg0shii's proof for L-meta-11970](https://github.com/open-goat/pequalnp-proofs/pull/16070)
