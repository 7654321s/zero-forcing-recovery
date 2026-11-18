module

/- Realize two terminal path pairs simultaneously in the checked two-center model. -/
public import «formalization-tree-terminal-pairs»
public import «formalization-two-center-clock»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u v
variable {V : Type u}

def twoPendantCongrIso {W : Type v} (R : SimpleGraph V) (S : SimpleGraph W)
    (e : R ≃g S) (x : V) (y : W) (hxy : e x = y) (a b : ℕ) :
    twoPendantGraph R x a b ≃g twoPendantGraph S y a b where
  toEquiv := Equiv.sumCongr e.toEquiv (Equiv.refl _)
  map_rel_iff' := by
    rintro (z | (i | j)) (w | (k | l))
    · exact e.map_adj_iff
    · change (e z = y ∧ k = 0) ↔ z = x ∧ k = 0
      rw [← hxy, e.injective.eq_iff]
    · change (e z = y ∧ l = 0) ↔ z = x ∧ l = 0
      rw [← hxy, e.injective.eq_iff]
    · change (e w = y ∧ i = 0) ↔ w = x ∧ i = 0
      rw [← hxy, e.injective.eq_iff]
    · rfl
    · rfl
    · change (e w = y ∧ j = 0) ↔ w = x ∧ j = 0
      rw [← hxy, e.injective.eq_iff]
    · rfl
    · rfl

theorem terminal_pairs_two_center_realization [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (a b : V) (hab : a ≠ b) (P : TerminalTreeCutPair G a b hab)
    (Q : TerminalTreeCutPair G b a hab.symm) :
    ∃ (W : Type u) (R : SimpleGraph W) (x y : W) (m n k l : ℕ),
      Finite W ∧ R.IsTree ∧ x ≠ y ∧ Nonempty (twoCenterGraph R x y m n k l ≃g G) ∧
      (R.Adj x y ↔ G.Adj b a) ∧
      m + 1 = Nat.card Q.first ∧ n + 1 = Nat.card Q.second ∧
      k + 1 = Nat.card P.first ∧ l + 1 = Nat.card P.second := by
  classical
  let S₁ := treeComponentRemainderSet G a ({P.first, P.second} : Set _)
  let R₁ := treeComponentRemainderGraph G a {P.first, P.second}
  let a₁ : S₁ := twoComponentCoreRoot G a P.first P.second
  have hR₁ : R₁.IsTree := tree_component_remainder_isTree G hG a {P.first, P.second}
  obtain ⟨hb, Q₁, hcard₁, hcard₂, _, _⟩ := terminal_pair_opposite_path_components G hG.connected a b hab P Q
  let b₁ : S₁ := ⟨b, hb⟩
  have hba : b₁ ≠ a₁ := fun h => hab.symm (congrArg Subtype.val h)
  let S₂ := treeComponentRemainderSet R₁ b₁ ({Q₁.first, Q₁.second} : Set _)
  let R₂ := treeComponentRemainderGraph R₁ b₁ {Q₁.first, Q₁.second}
  have ha : a₁ ∈ S₂ := by
    apply tree_off_components_keep_other_vertex R₁ b₁ a₁ hba.symm {Q₁.first, Q₁.second}
    intro C hC
    have hc : C = Q₁.first ∨ C = Q₁.second := by simpa using hC
    rcases hc with rfl | rfl
    · exact Q₁.first_off
    · exact Q₁.second_off
  let a₂ : S₂ := ⟨a₁, ha⟩
  let b₂ : S₂ := twoComponentCoreRoot R₁ b₁ Q₁.first Q₁.second
  obtain ⟨s, k, hs, e, he⟩ := P.first_path
  obtain ⟨t, l, ht, f, hf⟩ := P.second_path
  let e₁ : twoPendantGraph R₁ a₁ k l ≃g G :=
    twoCutPathsRealizationIso G hG a P.first P.second P.distinct k l s hs t ht e f he hf
  obtain ⟨s', m, hs', e', he'⟩ := Q₁.first_path
  obtain ⟨t', n, ht', f', hf'⟩ := Q₁.second_path
  let e₂ : twoPendantGraph R₂ b₂ m n ≃g R₁ :=
    twoCutPathsRealizationIso R₁ hR₁ b₁ Q₁.first Q₁.second Q₁.distinct m n
      s' hs' t' ht' e' f' he' hf'
  have hroot : e₂ (twoPendantCore S₂ m n a₂) = a₁ := rfl
  let e₃ := twoPendantCongrIso (twoPendantGraph R₂ b₂ m n) R₁ e₂
    (twoPendantCore S₂ m n a₂) a₁ hroot k l
  refine ⟨S₂, R₂, b₂, a₂, m, n, k, l, inferInstance,
    tree_component_remainder_isTree R₁ hR₁ b₁ {Q₁.first, Q₁.second}, ?_, ⟨e₃.trans e₁⟩,
    Iff.rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hba (congrArg Subtype.val h)
  · have hm : Nat.card Q₁.first = m + 1 := by
      simpa only [Nat.card_fin] using Nat.card_congr e'.toEquiv
    omega
  · have hn : Nat.card Q₁.second = n + 1 := by
      simpa only [Nat.card_fin] using Nat.card_congr f'.toEquiv
    omega
  · have hk : Nat.card P.first = k + 1 := by
      simpa only [Nat.card_fin] using Nat.card_congr e.toEquiv
    exact hk.symm
  · have hl : Nat.card P.second = l + 1 := by
      simpa only [Nat.card_fin] using Nat.card_congr f.toEquiv
    exact hl.symm

theorem terminal_pairs_prescribed_two_center_realization [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (a b : V) (hab : a ≠ b) (P : TerminalTreeCutPair G a b hab)
    (Q : TerminalTreeCutPair G b a hab.symm) (m n k l : ℕ)
    (hm : Nat.card Q.first = m + 1) (hn : Nat.card Q.second = n + 1)
    (hk : Nat.card P.first = k + 1) (hl : Nat.card P.second = l + 1) :
    ∃ (W : Type u) (R : SimpleGraph W) (x y : W),
      Finite W ∧ R.IsTree ∧ x ≠ y ∧ Nonempty (twoCenterGraph R x y m n k l ≃g G) ∧
      (R.Adj x y ↔ G.Adj b a) := by
  obtain ⟨W, R, x, y, m', n', k', l', hW, hR, hxy, e, hadj, hm', hn', hk', hl'⟩ :=
    terminal_pairs_two_center_realization G hG a b hab P Q
  have hmeq : m' = m := by omega
  have hneq : n' = n := by omega
  have hkeq : k' = k := by omega
  have hleq : l' = l := by omega
  subst m'
  subst n'
  subst k'
  subst l'
  exact ⟨W, R, x, y, hW, hR, hxy, e, hadj⟩

theorem finite_multi_branch_two_center_realization [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree)
    (hexists : ∃ a b, TreeBranchVertex G a ∧ TreeBranchVertex G b ∧ a ≠ b) :
    ∃ (W : Type u) (R : SimpleGraph W) (x y : W) (m n k l : ℕ),
      Finite W ∧ R.IsTree ∧ x ≠ y ∧ Nonempty (twoCenterGraph R x y m n k l ≃g G) := by
  obtain ⟨a, b, hab, _, _, ⟨P⟩, ⟨Q⟩⟩ := finite_two_terminal_path_pairs G hG hexists
  obtain ⟨W, R, x, y, m, n, k, l, hW, hR, hxy, e, _, _, _, _, _⟩ :=
    terminal_pairs_two_center_realization G hG a b hab P Q
  exact ⟨W, R, x, y, m, n, k, l, hW, hR, hxy, e⟩

end FaultObservationResearch
