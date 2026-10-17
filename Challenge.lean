/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# The Nash-Williams–Tutte tree packing theorem and Nash-Williams' arboricity theorem

For a finite simple graph `G` on `V`:

* `NashWilliamsTutte.tree_packing`: **Nash-Williams (1961), Tutte (1961).** `G` has `k` edge-disjoint
  spanning trees if and only if, for every partition of `V` into `m` parts, at least `k (m - 1)`
  edges of `G` join different parts. A partition is given by a map `f : V → V` (its parts are the
  nonempty fibres, `#(univ.image f)` of them), and the edges of `G` joining different parts are
  those of `G ⊓ (⊤ : SimpleGraph V).comap f`.
* `NashWilliamsTutte.arboricity`: **Nash-Williams (1964).** The edges of `G` can be covered by `k`
  forests if and only if every nonempty vertex set `S` spans at most `k (#S - 1)` edges.
* `NashWilliamsTutte.exists_trees_of_isEdgeConnected`: **corollary.** A `2k`-edge-connected finite
  graph (Mathlib's `SimpleGraph.IsEdgeConnected`) has `k` edge-disjoint spanning trees.

Spanning trees are subgraphs `T ≤ G` on the same vertex type with Mathlib's `SimpleGraph.IsTree`;
forests are subgraphs with `SimpleGraph.IsAcyclic`; edge-disjointness is `Disjoint` in the lattice
of simple graphs.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace NashWilliamsTutte

/-- **Nash-Williams–Tutte tree packing theorem.** A finite graph on a nonempty vertex type has `k`
pairwise edge-disjoint spanning trees if and only if, for every map `f : V → V`, the number of
edges of `G` whose endpoints have different images under `f` is at least `k` times the number of
nonempty fibres of `f` minus one. -/
theorem tree_packing {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    (k : ℕ) :
    (∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
        Pairwise fun i j ↦ Disjoint (T i) (T j)) ↔
      ∀ f : V → V,
        k * (#(univ.image f) - 1) ≤ (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet.ncard := by
  sorry

/-- **Nash-Williams' arboricity theorem.** The edges of a finite graph can be covered by `k`
forests if and only if every nonempty set `S` of vertices spans at most `k (#S - 1)` edges. -/
theorem arboricity {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) :
    (∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ G = ⨆ i, F i) ↔
      ∀ S : Finset V, S.Nonempty → (G.induce (S : Set V)).edgeSet.ncard ≤ k * (#S - 1) := by
  sorry

/-- **Corollary.** A finite `2k`-edge-connected graph on a nonempty vertex type has `k` pairwise
edge-disjoint spanning trees. -/
theorem exists_trees_of_isEdgeConnected {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (k : ℕ) (hG : G.IsEdgeConnected (2 * k)) :
    ∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
      Pairwise fun i j ↦ Disjoint (T i) (T j) := by
  sorry

end NashWilliamsTutte
