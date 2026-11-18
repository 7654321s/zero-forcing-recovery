module

/-
Original-tree bridge for a unique branching vertex with no leaf neighbors.
All original vertices and edges are transported by the verified realization.
-/
public import «formalization-path-star-all-long»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u v w

theorem treeLeaf_of_graph_iso {V : Type v} {W : Type w}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) (x : V)
    (hx : TreeLeaf G x) : TreeLeaf H (e x) := by
  obtain ⟨neighbor, hadj, huniq⟩ := hx
  refine ⟨e neighbor, e.map_adj_iff.mpr hadj, ?_⟩
  intro y hy
  have hp : G.Adj x (e.symm y) := e.map_adj_iff.mp (by simpa using hy)
  have heq := huniq (e.symm y) hp
  calc
    y = e (e.symm y) := (e.apply_symm_apply y).symm
    _ = e neighbor := congrArg e heq

variable {I : Type u} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem pathStar_length_one_is_leaf (L : I → ℕ) (i : I) (hL : L i = 1)
    (k : Fin (L i)) : TreeLeaf (pathStarGraph L) (some ⟨i, k⟩) := by
  have hk : k.val = 0 := by have h := k.isLt; omega
  refine ⟨none, hk, ?_⟩
  intro y hy
  cases y with
  | none => rfl
  | some y =>
    obtain ⟨j, l⟩ := y
    change i = j ∧ (k.val + 1 = l.val ∨ l.val + 1 = k.val) at hy
    obtain ⟨rfl, hleft | hright⟩ := hy <;> have hl := l.isLt <;> omega

theorem pathStar_branch_center_card (L : I → ℕ)
    (hbranch : TreeBranchVertex (pathStarGraph L) none) : 3 ≤ Fintype.card I := by
  classical
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hbranch
  cases a with
  | none => exact ha.elim
  | some a =>
    cases b with
    | none => exact hb.elim
    | some b =>
      cases c with
      | none => exact hc.elim
      | some c =>
        obtain ⟨i, k⟩ := a
        obtain ⟨j, l⟩ := b
        obtain ⟨m, n⟩ := c
        change k.val = 0 at ha
        change l.val = 0 at hb
        change n.val = 0 at hc
        have hij : i ≠ j := by
          intro h
          subst j
          apply hab
          have hkl : k = l := Fin.ext (ha.trans hb.symm)
          subst l
          rfl
        have him : i ≠ m := by
          intro h
          subst m
          apply hac
          have hkn : k = n := Fin.ext (ha.trans hc.symm)
          subst n
          rfl
        have hjm : j ≠ m := by
          intro h
          subst m
          apply hbc
          have hln : l = n := Fin.ext (hb.trans hc.symm)
          subst n
          rfl
        have hcard : ({i, j, m} : Finset I).card = 3 := by simp [hij, him, hjm]
        have hupper := Finset.card_le_univ ({i, j, m} : Finset I)
        omega

theorem finite_single_branch_no_leaf_neighbors_not_support {V : Type v}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.IsTree) (root : V)
    (hrootbranch : TreeBranchVertex G root)
    (hbranch : ∀ x, x ≠ root → ¬ TreeBranchVertex G x)
    (hnoleaf : ∀ x, G.Adj root x → ¬ TreeLeaf G x) :
    ¬ EveryMinimumSupport G.Adj := by
  classical
  let : Fintype (treeCutGraph G root).ConnectedComponent := Fintype.ofFinite _
  have hpaths := finite_single_branch_cut_components_paths G hG root hbranch
  choose a ha L hpos e he using hpaths
  let f := pathStarRealizationIso G hG root a ha L e he
  have hroot : f none = root := rfl
  have hsym : f.symm root = none := by
    apply f.injective
    rw [f.apply_symm_apply, hroot]
  have hmodelbranch : TreeBranchVertex (pathStarGraph L) none := by
    have h := branch_vertex_of_embedding G (pathStarGraph L) f.symm.toEmbedding root hrootbranch
    change TreeBranchVertex (pathStarGraph L) (f.symm root) at h
    simpa only [hsym] using h
  have hcard := pathStar_branch_center_card L hmodelbranch
  have hlong : ∀ i, 2 ≤ L i := by
    intro i
    by_contra h
    have hLi : L i = 1 := by have hp := hpos i; omega
    let k : Fin (L i) := ⟨0, by omega⟩
    have hleaf := treeLeaf_of_graph_iso (pathStarGraph L) G f (some ⟨i, k⟩)
      (pathStar_length_one_is_leaf L i hLi k)
    have hadj : G.Adj root (f (some ⟨i, k⟩)) := by
      have hmodel : (pathStarGraph L).Adj none (some ⟨i, k⟩) := rfl
      simpa only [hroot] using f.map_adj_iff.mpr hmodel
    exact hnoleaf _ hadj hleaf
  exact graph_iso_all_long_pathStar_not_support G L hlong hcard f.symm

end FaultObservationResearch
