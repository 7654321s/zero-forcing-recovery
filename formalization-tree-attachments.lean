module

/-
Attaching paths preserves the tree property. The sum-and-bridge argument is
standard graph theory. It discharges the construction hypothesis of the checked
two-center strict family, not arbitrary-tree structural exhaustion or priority.
-/
public import «formalization-two-center-clock»
public import Mathlib.Combinatorics.SimpleGraph.Sum

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u v

def bridgeJoin {V : Type u} {W : Type v} (G : SimpleGraph V) (H : SimpleGraph W)
    (x : V) (y : W) : SimpleGraph (V ⊕ W) :=
  G.sum H ⊔ SimpleGraph.edge (Sum.inl x) (Sum.inr y)

theorem bridgeJoin_isTree {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : G.IsTree) (hH : H.IsTree)
    (x : V) (y : W) : (bridgeJoin G H x y).IsTree := by
  classical
  have hsum : (G.sum H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
    simp only [SimpleGraph.edgeFinset_card]
    have hm := Fintype.card_congr (SimpleGraph.edgeSetSumEquiv (G := G) (H := H))
    simpa only [Fintype.card_sum] using hm
  have hedge := (G.sum H).card_edgeFinset_sup_edge
    (s := Sum.inl x) (t := Sum.inr y) (by simp) (by simp)
  have hg := hG.card_edgeFinset
  have hh := hH.card_edgeFinset
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hsum hedge hg hh
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hG.connected.sum_sup_edge hH.connected, ?_⟩
  change Nat.card (G.sum H ⊔ SimpleGraph.edge (Sum.inl x) (Sum.inr y)).edgeSet + 1 = _
  rw [hedge, hsum, Nat.card_sum]
  omega

def twoPendantAsBridgeIso {V : Type u} (R : SimpleGraph V) (root : V) (a b : ℕ) :
    twoPendantGraph R root a b ≃g
      bridgeJoin (bridgeJoin R (SimpleGraph.pathGraph (a + 1)) root 0)
        (SimpleGraph.pathGraph (b + 1)) (Sum.inl root) 0 where
  toEquiv := (Equiv.sumAssoc V (Fin (a + 1)) (Fin (b + 1))).symm
  map_rel_iff' := by
    rintro (x | (i | j)) (y | (k | l)) <;>
      simp [bridgeJoin, SimpleGraph.sum, SimpleGraph.edge_adj, Equiv.sumAssoc,
        twoPendantGraph, twoPendantAdj, eq_comm] <;> exact and_comm

theorem twoPendantGraph_isTree {V : Type u} [Fintype V]
    (R : SimpleGraph V) (htree : R.IsTree) (root : V) (a b : ℕ) :
    (twoPendantGraph R root a b).IsTree := by
  have hA := bridgeJoin_isTree R (SimpleGraph.pathGraph (a + 1)) htree
    (SimpleGraph.isTree_pathGraph_add_one a) root 0
  have hB := bridgeJoin_isTree
    (bridgeJoin R (SimpleGraph.pathGraph (a + 1)) root 0)
    (SimpleGraph.pathGraph (b + 1)) hA (SimpleGraph.isTree_pathGraph_add_one b)
    (Sum.inl root) 0
  exact (twoPendantAsBridgeIso R root a b).isTree_iff.mpr hB

theorem twoCenterGraph_isTree {V : Type u} [Fintype V]
    (R : SimpleGraph V) (htree : R.IsTree) (u v : V) (a b c d : ℕ) :
    (twoCenterGraph R u v a b c d).IsTree :=
  twoPendantGraph_isTree (twoPendantGraph R u a b)
    (twoPendantGraph_isTree R htree u a b) (twoPendantCore V a b v) c d

theorem twoCenter_strict_tree_witness {V : Type u} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) (htree : R.IsTree) (u v : V) (hvu : v ≠ u)
    (a b c d : ℕ) (hstrict : max (c + 1) (d + 1) < a + b + 1) :
    (twoCenterGraph R u v a b c d).IsTree ∧
      ¬ EveryMinimumSupport (twoCenterGraph R u v a b c d).Adj := by
  exact ⟨twoCenterGraph_isTree R htree u v a b c d,
    twoCenter_strict_not_support R u v hvu a b c d
      (twoPendantGraph_isTree R htree u a b) hstrict⟩

end FaultObservationResearch
