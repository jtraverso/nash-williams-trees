/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import TreePackingLib.NashWilliams

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `TreePackingLib/NashWilliams.lean` and
`TreePackingLib/NashWilliamsAux.lean` (namespace `NashWilliams`) by a direct edge-exchange argument
in the style of Diestel's proof: among `k` edge-disjoint forests with the maximum number of edges,
the edges that can be freed by sequences of single-edge exchanges form a graph `H` whose components
are spanned by every forest. The tree packing theorem then follows by counting edges between the
components of `H`, the arboricity theorem by counting edges inside a component of `H`, and the
corollary by counting the edges leaving each part of a partition of a `2k`-edge-connected graph.
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
        k * (#(univ.image f) - 1) ≤ (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet.ncard :=
  NashWilliams.tree_packing G k

/-- **Nash-Williams' arboricity theorem.** The edges of a finite graph can be covered by `k`
forests if and only if every nonempty set `S` of vertices spans at most `k (#S - 1)` edges. -/
theorem arboricity {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) :
    (∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ G = ⨆ i, F i) ↔
      ∀ S : Finset V, S.Nonempty → (G.induce (S : Set V)).edgeSet.ncard ≤ k * (#S - 1) :=
  NashWilliams.arboricity G k

/-- **Corollary.** A finite `2k`-edge-connected graph on a nonempty vertex type has `k` pairwise
edge-disjoint spanning trees. -/
theorem exists_trees_of_isEdgeConnected {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (k : ℕ) (hG : G.IsEdgeConnected (2 * k)) :
    ∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
      Pairwise fun i j ↦ Disjoint (T i) (T j) :=
  NashWilliams.exists_trees_of_isEdgeConnected G k hG

end NashWilliamsTutte
