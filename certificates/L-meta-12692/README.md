# Minimum circuits for a block of OR-equivalent inputs

Let $k\ge1$, let $Z=z_1\lor\cdots\lor z_k$, and define

```text
F_k(a,b,c,d,z_1,...,z_k) =
    [Z AND (a OR (c AND d))] OR [b AND (c OR d) AND (a OR Z)].
```

The case $k=2$ is the six-input truth table `0xfeeafeeafeea8880` from L-meta-12691/12692. In the project's fan-in-two AND/OR/NOT model, the minimum total gate count is **k + 7**, even with a zero budget for NOT. The number of minimum **monotone** circuits with fixed input names is

```text
N(k) = 9 D(k) + 3 D(k+1) = 6(k+1) D(k)
D(1) = 1,   D(k+1) = (2k-1) D(k).
```

Here $D(k)=(2k-3)!!$ counts rooted binary OR trees on the $k$ distinct inputs, with unordered children. The circuit count identifies gate schedules and operand swaps. It distinguishes different graphs related by associativity or permutations of input names. Wires may have multiple consumers.

| Block size | Minimum gates | Minimum monotone circuits | Have a wire equal to Z |
|---:|---:|---:|---:|
| 1 | 8 | 12 | 12 |
| 2 | 9 | 18 | 12 |
| 3 | 10 | 72 | 36 |
| 4 | 11 | 450 | 180 |
| 5 | 12 | 3,780 | 1,260 |

Every minimum monotone circuit has a wire reached from **all** the block inputs using only OR gates. Exactly $12D(k)$ circuits actually compute $Z$ on one wire. The distinction is already visible with two inputs. Twelve circuits have a gate computing $z_1\lor z_2$. Six instead have an OR subtree such as $z_1\lor(z_2\lor H)$, with $H=a\land b\land(c\lor d)$. Of the eighteen nine-gate circuits, one has depth four, eight have depth five and nine have depth six.

## Size and the five-input catalogue

A circuit for $F_1$ needs at least eight gates by [nicohabets's five-input lower bound](https://github.com/open-goat/pequalnp-proofs/pull/17465), reproduced on the branch's parent. All twelve listed cores are eight-gate monotone witnesses. Each OR split of the named input is essential, as seen by setting $a=1$, $b=c=d=0$ and the other block inputs to zero. Splitting an essential input adds exactly one gate under any fixed upper bound on the number of NOT gates. The Lean theorem `exact_block_cost` covers the whole OR family. The file instantiates the [previous split theorem](https://github.com/Simlowker/pequalnp-proofs/tree/53d439e6b0e8a818a0f9373e915a54c27e40aa22/certificates/L-meta-11971), which uses hilelyos's gate-elimination infrastructure in L-meta-9526. For the original six-input case, [Leg0shii's independent proof](https://github.com/open-goat/pequalnp-proofs/pull/16776) gives a lower bound of nine on the number of non-NOT gates, so every minimum circuit in that case is monotone.

The finite base is exhausted by a checked LRAT refutation. In a minimum monotone network for this nonconstant function, delete unused gates, constant gates, gates with only one effective input, and repeated gates by substituting their values in consumers. Any such deletion would contradict minimum size. Invalid reads in the project model have the constant value false and simplify in the same way. The normalized network therefore has two distinct earlier operand wires per gate, all gates lead to the output, and the output is the last gate. Every primary input is essential. To canonically number gates, repeatedly choose a ready gate of minimum key (larger operand index, smaller operand index, operation), with AND before OR. A newly ready gate uses the just-numbered wire, so its larger operand exceeds that of the gate just chosen. Equal keys would be duplicate gates. The resulting keys are strictly increasing; conversely a schedule with increasing keys makes these same choices.

The encoding fixes exactly one operation and ordered pair of sources per gate. It enforces the keys and uses above. Since both the networks and target are monotone, matching all minimal true and maximal false rows determines the entire table. One clause blocks each listed wiring and operation sequence. Refuting the residual CNF proves completeness; the verifier also tests every listed network on its entire truth table.

## Inserting one fresh input

Pin a new block variable $y$ to false in any minimum monotone circuit for $F_{k+1}$. At least one gate reads $y$, because it is essential and the output depends on other inputs. Every gate directly reading $y$ is removed by constant propagation. The minimum for $F_k$ is exactly one smaller, so only one gate is removed. If that gate were AND, it would produce constant false. It cannot be the output, since $F_k$ is nonconstant, and it has a consumer, since the original network is minimum. That consumer would also simplify, contradicting the lower bound. Thus the removed gate is an OR of $y$ with an existing wire $v$.

Consequently every minimum circuit for $F_{k+1}$ is obtained from a minimum circuit for $F_k$ by adding $y\lor v$ and redirecting a nonempty subset of the uses of $v$ to it. Uses include individual operand ports and the designated output. This also covers multiple consumers. Setting $y=0$ recovers the old program. For $y=1$ the redirected ports carry true, so a proposed attachment is valid exactly when the altered truth table agrees with the target having $Z=1$.

For each of the twelve cores, `TwinAtlas.lean` exhausts every one of these port subsets. The cores appear in `cores.json` in the same order as the Lean list; indices below start at zero. There are exactly two outcomes.

* In nine cores the sole valid operation places the new OR above $z$ and redirects **all** uses of $z$. In some cores $z$ has two consumers, making this quantifier consequential.
* In cores 6, 7 and 10 there is a single-use wire $H=a\land b\land(c\lor d)$, a single-use input $z$, and a single-use OR joint $J=z\lor H$. The three possible grafts go above $z$, above $H$, or above $J$. The checked attachment table gives the exact operand ports in each case.

## Induction on the whole circuit shape

For each of the nine cores of the first kind, replace its input $z$ by any binary OR tree on the block inputs and connect its root to all the original uses of $z$. For each of the three cores of the second kind, replace the joint $J$ by any binary OR tree whose leaves are the block inputs and the distinguished wire $H$. Each construction computes $F_k$ using $k+7$ gates.

To see that these are all the possibilities, take the one-gate insertion described above. In the first kind, grafting inside the tree (including a leaf) extends that tree by the new leaf. Every proper subtree has one consumer. A graft on its root may redirect several consumers; a graft on any external wire may affect an arbitrary subset of its ports. Contract the tree to a single input $z$ to test such a choice. Its effect on the exterior is exactly the effect on the core: the tree presents only $Z$ and both values of $Z$ are attainable independently of the four external inputs. The finite attachment table therefore requires grafting on the root and redirecting all its uses. For $k=1$ the root is the original input.

In the second kind the entire replaced region presents only $Z\lor H$ to the exterior. Its proper internal wires and its two boundaries (the $H$ wire and the root) each have one consumer. Grafting at any of these positions, or at a block leaf, gives another OR tree with the extra block leaf. For a graft elsewhere, contract that region back to $z\lor H$. An outside change may alter $H$ via its ancestors; the region still presents precisely the disjunction of the altered $H$ and the independent block value. Hence the changed core would pass the same test with $y=1$. Its only three permitted positions are already on the region. This proves the induction step without a bound on $k$.

Assignments with all but one block input pinned false reduce each construction back to its own core after suppressing the resulting identities, so constructions from different cores are distinct. Within a core of the first kind the root is the unique wire computing $Z$; within the second kind it is the unique wire computing $Z\lor H$. Uniqueness follows from minimum size: two wires computing the same function would let one remove the later gate by substitution. Unfolding the OR tree at that root recovers its topology and labelled leaves, stopping at the designated $H$ in the second kind. A binary tree on $k$ named leaves has $2k-2$ edges plus the position above its root at which to insert a new named leaf. Removing that leaf reverses the insertion, giving the recurrence for $D(k)$ and the stated count.

In a mixed tree a pure $Z$ wire exists exactly when all block leaves form one subtree, with $H$ its sibling. Outside the tree, downstream wires see the block only via $Z\lor H$. Setting $H=1$ while varying $Z$ excludes any such wire from computing $Z$. This proves the last column of the table.

## Reproduction

In the repository's `lean/` directory:

```sh
lake build PEqualNP.Outside.L_meta_12691 PEqualNP.Outside.L_meta_9526
lake env lean ../certificates/L-meta-12692/TwinAtlas.lean
```

In this certificate directory:

```sh
python3 verify.py
zstd -dc cores.lrat.zst | lrat-trim --no-trim --rup cores.cnf -
python3 grow.py --twins 5
```

The five-input refutation takes 199,815 RUP additions. The checker prints `s VERIFIED` and exits with status 20. The saved proof was also replayed by a separate RUP implementation. For an independent six-input check, `python3 verify.py --six-cnf six.cnf` reconstructs the fully blocked formula. Running `cadical --lrat --no-binary six.cnf six.lrat` and checking the result independently verifies the eighteen-network count. The six-input trimmed proof was replayed locally (1,248,653 RUP additions). The five-input certificate and the insertion argument suffice for the family result. [lrat-trim version used](https://github.com/arminbiere/lrat-trim/tree/423194927df747528d5b7364806b5b77b2660c12)

The Lean kernel verifies the size bound at every NOT budget, the twelve witnesses, and the complete finite port-attachment table. The exhaustive core count uses the supplied CNF and external LRAT certificate. The general topology classification and labelled count use the induction above. The negative gap L-meta-12692 hypothesizes a saving from NOT for this function; the results here support its positive twin.
