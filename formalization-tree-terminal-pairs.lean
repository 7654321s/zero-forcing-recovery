module

/- Terminal branch vertices supply two disjoint rooted path components each. -/
public import «formalization-tree-branch-diameter»
public import «formalization-tree-opposite-components»
public import «formalization-retained-component»
public import «formalization-tree-two-component-realization»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u}

def RootedTreeCutPath (G : SimpleGraph V) (root : V)
    (C : (treeCutGraph G root).ConnectedComponent) : Prop :=
  ∃ (a : C) (n : ℕ), G.Adj root a.val.val ∧
    ∃ e : C.toSimpleGraph ≃g SimpleGraph.pathGraph (n + 1), (e a).val = 0

structure TerminalTreeCutPair (G : SimpleGraph V) (root other : V) (hne : root ≠ other) where
  first : (treeCutGraph G root).ConnectedComponent
  second : (treeCutGraph G root).ConnectedComponent
  distinct : first ≠ second
  first_off : (⟨other, hne.symm⟩ : TreeCutVertex root) ∉ first.supp
  second_off : (⟨other, hne.symm⟩ : TreeCutVertex root) ∉ second.supp
  first_path : RootedTreeCutPath G root first
  second_path : RootedTreeCutPath G root second

theorem rooted_cut_path_of_positive_length (G : SimpleGraph V) (root : V)
    (C : (treeCutGraph G root).ConnectedComponent)
    (h : ∃ a : C, G.Adj root a.val.val ∧ ∃ n, 1 ≤ n ∧
      ∃ e : C.toSimpleGraph ≃g SimpleGraph.pathGraph n, (e a).val = 0) :
    RootedTreeCutPath G root C := by
  obtain ⟨a, ha, n, hn, e, he⟩ := h
  cases n with
  | zero => omega
  | succ n => exact ⟨a, n, ha, e, he⟩

theorem finite_two_terminal_path_pairs [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (hexists : ∃ a b, TreeBranchVertex G a ∧ TreeBranchVertex G b ∧ a ≠ b) :
    ∃ (a b : V) (hab : a ≠ b), TreeBranchVertex G a ∧ TreeBranchVertex G b ∧
      Nonempty (TerminalTreeCutPair G a b hab) ∧
      Nonempty (TerminalTreeCutPair G b a hab.symm) := by
  classical
  obtain ⟨a, b, hab, p, ha, hb, _, _, hleft, hright⟩ :=
    finite_terminal_branch_path_components G hG hexists
  obtain ⟨C, D, hCD, hC, hD⟩ := branch_vertex_two_off_components G hG a b hab ha
  obtain ⟨E, F, hEF, hE, hF⟩ := branch_vertex_two_off_components G hG b a hab.symm hb
  refine ⟨a, b, hab, ha, hb, ?_, ?_⟩
  · exact ⟨⟨C, D, hCD, hC, hD, rooted_cut_path_of_positive_length G a C (hleft C hC),
      rooted_cut_path_of_positive_length G a D (hleft D hD)⟩⟩
  · exact ⟨⟨E, F, hEF, hE, hF, rooted_cut_path_of_positive_length G b E (hright E hE),
      rooted_cut_path_of_positive_length G b F (hright F hF)⟩⟩

theorem terminal_pair_opposite_first_kept (G : SimpleGraph V) (hG : G.Connected)
    (a b : V) (hab : a ≠ b) (P : TerminalTreeCutPair G a b hab)
    (Q : TerminalTreeCutPair G b a hab.symm) (x : Q.first) :
    x.val.val ∈ treeComponentRemainderSet G a ({P.first, P.second} : Set _) := by
  apply opposite_off_component_kept G hG a b hab {P.first, P.second} _ Q.first Q.first_off x
  intro C hC
  have hc : C = P.first ∨ C = P.second := by simpa using hC
  rcases hc with rfl | rfl
  · exact P.first_off
  · exact P.second_off

theorem terminal_pair_opposite_second_kept (G : SimpleGraph V) (hG : G.Connected)
    (a b : V) (hab : a ≠ b) (P : TerminalTreeCutPair G a b hab)
    (Q : TerminalTreeCutPair G b a hab.symm) (x : Q.second) :
    x.val.val ∈ treeComponentRemainderSet G a ({P.first, P.second} : Set _) := by
  apply opposite_off_component_kept G hG a b hab {P.first, P.second} _ Q.second Q.second_off x
  intro C hC
  have hc : C = P.first ∨ C = P.second := by simpa using hC
  rcases hc with rfl | rfl
  · exact P.first_off
  · exact P.second_off

theorem terminal_pair_two_pendant_realization (G : SimpleGraph V) (hG : G.IsTree)
    (a b : V) (hab : a ≠ b) (P : TerminalTreeCutPair G a b hab) :
    ∃ m n : ℕ, Nonempty (twoPendantGraph
      (treeComponentRemainderGraph G a {P.first, P.second})
      (twoComponentCoreRoot G a P.first P.second) m n ≃g G) := by
  obtain ⟨x, m, hx, e, he⟩ := P.first_path
  obtain ⟨y, n, hy, f, hf⟩ := P.second_path
  exact ⟨m, n, ⟨twoCutPathsRealizationIso G hG a P.first P.second P.distinct m n
    x hx y hy e f he hf⟩⟩

theorem rooted_cut_path_retained (G : SimpleGraph V) (S : Set V) (root : V)
    (hroot : root ∈ S) (C : (treeCutGraph G root).ConnectedComponent)
    (hC : ∀ x : C, x.val.val ∈ S) (a : C) (hpath : RootedTreeCutPath G root C) :
    RootedTreeCutPath (G.induce S) (⟨root, hroot⟩ : S)
      (retainedCutComponent G S root hroot C hC a) := by
  obtain ⟨x, n, hx, e, he⟩ := hpath
  let f := retainedCutComponentIso G S root hroot C hC a
  refine ⟨f x, n, ?_, f.symm.trans e, ?_⟩
  · change G.Adj root (f x).val.val.val
    rw [retainedCutComponentIso_apply_val]
    exact hx
  · change (e (f.symm (f x))).val = 0
    rw [f.symm_apply_apply]
    exact he

theorem terminal_pair_opposite_path_components (G : SimpleGraph V) (hG : G.Connected)
    (a b : V) (hab : a ≠ b) (P : TerminalTreeCutPair G a b hab)
    (Q : TerminalTreeCutPair G b a hab.symm) :
    ∃ hb : b ∈ treeComponentRemainderSet G a ({P.first, P.second} : Set _),
      ∃ Q₁ : TerminalTreeCutPair (treeComponentRemainderGraph G a {P.first, P.second})
        (⟨b, hb⟩ : treeComponentRemainderSet G a ({P.first, P.second} : Set _))
        (twoComponentCoreRoot G a P.first P.second)
        (fun h => hab.symm (congrArg Subtype.val h)),
        Nat.card Q₁.first = Nat.card Q.first ∧ Nat.card Q₁.second = Nat.card Q.second ∧
        (∀ z, z ∈ Q₁.first.supp ↔ cutInducedForgetHom G _ b hb z ∈ Q.first.supp) ∧
        (∀ z, z ∈ Q₁.second.supp ↔ cutInducedForgetHom G _ b hb z ∈ Q.second.supp) := by
  let S := treeComponentRemainderSet G a ({P.first, P.second} : Set _)
  have hb : b ∈ S := by
    apply tree_off_components_keep_other_vertex G a b hab.symm {P.first, P.second}
    intro C hC
    have hc : C = P.first ∨ C = P.second := by simpa using hC
    rcases hc with rfl | rfl
    · exact P.first_off
    · exact P.second_off
  have hE : ∀ x : Q.first, x.val.val ∈ S := terminal_pair_opposite_first_kept G hG a b hab P Q
  have hF : ∀ x : Q.second, x.val.val ∈ S := terminal_pair_opposite_second_kept G hG a b hab P Q
  obtain ⟨x, hx⟩ := Q.first.nonempty_supp
  obtain ⟨y, hy⟩ := Q.second.nonempty_supp
  let s : Q.first := ⟨x, hx⟩
  let t : Q.second := ⟨y, hy⟩
  let Q₁ : TerminalTreeCutPair (G.induce S) (⟨b, hb⟩ : S)
      (twoComponentCoreRoot G a P.first P.second)
      (fun h => hab.symm (congrArg Subtype.val h)) := {
    first := retainedCutComponent G S b hb Q.first hE s
    second := retainedCutComponent G S b hb Q.second hF t
    distinct := retained_cut_components_distinct G S b hb Q.first Q.second Q.distinct hE hF s t
    first_off := retained_cut_component_avoids G S b a hb
      (tree_component_remainder_root_mem G a {P.first, P.second}) hab Q.first hE s Q.first_off
    second_off := retained_cut_component_avoids G S b a hb
      (tree_component_remainder_root_mem G a {P.first, P.second}) hab Q.second hF t Q.second_off
    first_path := rooted_cut_path_retained G S b hb Q.first hE s Q.first_path
    second_path := rooted_cut_path_retained G S b hb Q.second hF t Q.second_path }
  exact ⟨hb, Q₁, (Nat.card_congr (retainedCutComponentIso G S b hb Q.first hE s).toEquiv).symm,
    (Nat.card_congr (retainedCutComponentIso G S b hb Q.second hF t).toEquiv).symm,
    retained_cut_component_mem_iff G S b hb Q.first hE s,
    retained_cut_component_mem_iff G S b hb Q.second hF t⟩

end FaultObservationResearch
