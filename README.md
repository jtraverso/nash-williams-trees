# The Nash-Williams–Tutte tree packing theorem and Nash-Williams' arboricity theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

This repository formalizes three classical results on finite simple graphs. None of them is in
Mathlib.

1. **Tree packing theorem (Nash-Williams 1961, Tutte 1961)** (`NashWilliamsTutte.tree_packing`).
   A graph has `k` edge-disjoint spanning trees if and only if every partition of its vertices
   into `m` parts has at least `k(m − 1)` edges between different parts.
2. **Arboricity theorem (Nash-Williams 1964)** (`NashWilliamsTutte.arboricity`). The edges of a
   graph can be covered by `k` forests if and only if every nonempty vertex set `S` spans at most
   `k(|S| − 1)` edges.
3. **Corollary** (`NashWilliamsTutte.exists_trees_of_isEdgeConnected`). Every `2k`-edge-connected
   graph has `k` edge-disjoint spanning trees.

How the notions are expressed in Lean:
- **Spanning trees** are subgraphs `T ≤ G` with Mathlib's `IsTree`.
- **Forests** are subgraphs with `IsAcyclic`.
- **Edge-disjointness** is `Disjoint`.
- **A partition** is given by a map `f : V → V`, whose parts are its nonempty fibres. Its crossing
  edges are those of `G ⊓ (⊤ : SimpleGraph V).comap f`.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and the [`TreePackingLib/`](TreePackingLib) folder: the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

Mathlib has no matroid union theorem and no graphic matroid. The proofs therefore use a direct
edge-exchange argument in the style of Diestel's proof of the tree packing theorem:

1. Take `k` edge-disjoint forests in `G` with the largest possible total number of edges.
2. Let `H` be the graph of the edges that become uncovered in some family reachable from this one
   by single-edge exchanges.
3. Every forest restricted to `H` connects exactly the same pairs of vertices as `H`, and every
   edge of `G` outside `H` is covered by the forests.

The three results then follow by counting:

- **Tree packing.** Apply the hypothesis to the partition into the components of `H`.
- **Arboricity.** If some edge were uncovered, then every forest would span its `H`-component `S`.
  So `G[S]` would have more than `k(|S| − 1)` edges, contradicting the hypothesis.
- **Corollary.** In a `2k`-edge-connected graph, at least `2k` edges leave each part of a
  partition. Summing over the parts gives at least `km` crossing edges.

## Sources

* C. St. J. A. Nash-Williams, *Edge-disjoint spanning trees of finite graphs*, J. London Math.
  Soc. 36 (1961) 445–450, doi:10.1112/jlms/s1-36.1.445.
* W. T. Tutte, *On the problem of decomposing a graph into n connected factors*, J. London Math.
  Soc. 36 (1961) 221–230, doi:10.1112/jlms/s1-36.1.221.
* C. St. J. A. Nash-Williams, *Decomposition of finite graphs into forests*, J. London Math. Soc.
  39 (1964) 12, doi:10.1112/jlms/s1-39.1.12.
* B. Chen, M. Matsumoto, J. Wang, Z. Zhang, J. Zhang, *A short proof of Nash-Williams' theorem for
  the arboricity of a graph*, Graphs Combin. 10 (1994) 27–28, doi:10.1007/BF01202467.

## Authorship and use of AI

The author chose the results. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
