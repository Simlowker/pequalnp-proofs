# Read-one incidence circuits

For any rectangle-free point–line incidence graph with at most three points or at most three lines, every binary AND/OR circuit detecting a selected incidence admits a read-one replacement of at most the same size. The other side can have arbitrary finite size.

The theorem in `ReadOneThreeSides.lean` is a restricted result for the project assignment L-meta-2585. The full assignment allows both sides to have arbitrary size. For every prime implicant, read-one means that one accepting proof tree reads each variable of that implicant at most once.

The finite part checks all 512 incidence masks. Three representatives need explicit circuit lower bounds. They have masks 87, 94 and 238 in row-major bit order. Their minimum gate counts are 7, 7 and 8. The lower bounds use RUP certificates checked by the Lean kernel. The upper bounds follow by covering the edges with the three points.

For arbitrary line count and three points, the proof classifies the possible column neighborhoods. Either two vertices cover every incidence, or three columns support a matching and all other occupied columns have degree one. Fixing those outside columns to false saves at least one gate per removed column. The retained 3-by-3 instance supplies the lower bound. Transposing handles the case of three lines.

## Reproduce

Use the Lean project in [open-goat/pequalnp-proofs at the tested upstream revision](https://github.com/open-goat/pequalnp-proofs/tree/a4bbd50801b635c41ce4ad600130b085b838a81a/lean) with its Mathlib and PEqualNP.Defs dependencies built. Run `./check.sh /absolute/path/to/pequalnp-proofs/lean` with the project's Lake and Lean toolchain available. The script compiles each source in dependency order, then prints the theorem's axioms. The replay can take several minutes. Certificate data are included in the Lean files.

The star-cover construction is upstream L-meta-7684. The converse covering bound and graph encoding come from L-meta-4897. L-meta-4805 connects circuits to the exact synthesis CNF. The verified RUP checker comes from the L-meta-5531 source. The wire-renaming argument follows R-meta-1934-271. L-meta-5720 supplies the strict gate saving under a nonconstant essential-input restriction in the arbitrary-side extension. Earlier local work on L-meta-3722 supplies the support and four-vertex-path lower bounds. The PEqualNP sources are redistributed under the included Apache-2.0 license.

The SAT solver supplied proof data. Each finite contradiction and its application to circuits is checked in Lean.
