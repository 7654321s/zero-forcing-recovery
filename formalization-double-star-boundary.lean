module

/-
The DS(1,b) obstruction for every b >= 2, with arbitrary-label transport.
This is a component of the candidate tree classification. The complete
DoubleStarTarget and full tree classification remain unproved.
Compilation records bind the exact checked source; no novelty claim is made.
-/
public import «formalization-tree-target»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

universe u

variable {I : Type u} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem allLeavesBlue_sdiff_sparse (amount : I → ℕ)
    (blue loss : Finset (CoronaVertex I amount)) (hall : AllLeavesBlue amount blue)
    (hcard : loss.card ≤ 1) : LeafSparse amount (blue \ loss) := by
  classical
  intro i j k hj hk
  have hjL : coronaLeaf amount i j ∈ loss := by
    by_contra h
    exact hj (Finset.mem_sdiff.mpr ⟨hall i j, h⟩)
  have hkL : coronaLeaf amount i k ∈ loss := by
    by_contra h
    exact hk (Finset.mem_sdiff.mpr ⟨hall i k, h⟩)
  exact coronaLeaf_injective amount i (Finset.card_le_one.mp hcard _ hjL _ hkL)

omit [Fintype I] in
theorem sparse_exists_blue_leaf_local (amount : I → ℕ)
    (blue : Finset (CoronaVertex I amount)) (hsparse : LeafSparse amount blue)
    (i : I) (hi : 2 ≤ amount i) : ∃ j : Fin (amount i), coronaLeaf amount i j ∈ blue := by
  classical
  by_contra hnone
  have hwhite : ∀ j : Fin (amount i), coronaLeaf amount i j ∉ blue := by
    intro j hj
    exact hnone ⟨j, hj⟩
  let j : Fin (amount i) := ⟨0, by omega⟩
  let k : Fin (amount i) := ⟨1, by omega⟩
  have heq := hsparse i j k (hwhite j) (hwhite k)
  have hv := congrArg Fin.val heq
  change (0 : ℕ) = 1 at hv
  exact Nat.zero_ne_one hv

theorem corona_finishes_two_of_leaf_witnesses (core : SimpleGraph I) (amount : I → ℕ)
    (blue : Finset (CoronaVertex I amount)) (hsparse : LeafSparse amount blue)
    (hwitness : ∀ i : I, ∃ j : Fin (amount i), coronaLeaf amount i j ∈ blue) :
    FinishesBy (coronaAdj core amount) blue 2 := by
  classical
  have hcores : ∀ i : I, Sum.inl i ∈ synchronousStep (coronaAdj core amount) blue := by
    intro i
    obtain ⟨j, hj⟩ := hwitness i
    exact core_mem_step_of_blue_leaf core amount blue i j hj
  have hnext := leafSparse_mono amount hsparse (subset_synchronousStep (coronaAdj core amount) blue)
  change synchronousStep (coronaAdj core amount)
    (synchronousStep (coronaAdj core amount) blue) = Finset.univ
  apply Finset.eq_univ_of_forall
  intro v
  cases v with
  | inl i => exact subset_synchronousStep _ _ (hcores i)
  | inr leaf =>
    rcases leaf with ⟨i, j⟩
    exact leaf_mem_step_of_cores_blue core amount _ hnext hcores i j

theorem corona_leaf_not_step_of_core_white (core : SimpleGraph I) (amount : I → ℕ)
    (blue : Finset (CoronaVertex I amount)) (i : I) (j : Fin (amount i))
    (hleaf : coronaLeaf amount i j ∉ blue) (hcore : Sum.inl i ∉ blue) :
    coronaLeaf amount i j ∉ synchronousStep (coronaAdj core amount) blue := by
  intro hm
  rcases (mem_synchronousStep _ _ _).mp hm with hold | ⟨source, hs, ha, _⟩
  · exact hleaf hold
  · cases source with
    | inl k =>
      change k = i at ha
      subst k
      exact hcore hs
    | inr leaf => exact False.elim ha

def broomLeafCount (b : ℕ) (i : Fin 2) : ℕ := if i = 0 then 1 else b

abbrev BroomVertex (b : ℕ) := CoronaVertex (Fin 2) (broomLeafCount b)

def broomAdj (b : ℕ) : BroomVertex b → BroomVertex b → Prop :=
  coronaAdj (⊤ : SimpleGraph (Fin 2)) (broomLeafCount b)

def broomLeaves (b : ℕ) : Finset (BroomVertex b) := by
  classical
  exact Finset.univ.filter (fun x => match x with | Sum.inl _ => False | Sum.inr _ => True)

def broomShortLeaf (b : ℕ) : BroomVertex b := coronaLeaf (broomLeafCount b) 0 (0 : Fin 1)

def broomLongLeaf (b : ℕ) (j : Fin b) : BroomVertex b :=
  coronaLeaf (broomLeafCount b) 1 j

theorem broom_all_leaves_blue (b : ℕ) : AllLeavesBlue (broomLeafCount b) (broomLeaves b) := by
  classical
  intro i j
  simp [broomLeaves, coronaLeaf]

theorem broom_short_ne_long (b : ℕ) (j : Fin b) : broomShortLeaf b ≠ broomLongLeaf b j := by
  intro h
  have hindex := congrArg Sigma.fst (Sum.inr.inj h)
  change (0 : Fin 2) = 1 at hindex
  exact (by decide : (0 : Fin 2) ≠ 1) hindex

theorem fin_two_vertex_cases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
  exact Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩

theorem broom_loss_sparse (b : ℕ) (loss : Finset (BroomVertex b)) (hcard : loss.card ≤ 1) :
    LeafSparse (broomLeafCount b) (broomLeaves b \ loss) :=
  allLeavesBlue_sdiff_sparse _ _ _ (broom_all_leaves_blue b) hcard

theorem broom_loss_two_of_short_retained (b : ℕ) (hb : 2 ≤ b)
    (loss : Finset (BroomVertex b)) (hcard : loss.card ≤ 1)
    (hshort : broomShortLeaf b ∉ loss) :
    FinishesBy (broomAdj b) (broomLeaves b \ loss) 2 := by
  classical
  apply corona_finishes_two_of_leaf_witnesses (⊤ : SimpleGraph (Fin 2))
    (broomLeafCount b) _ (broom_loss_sparse b loss hcard)
  rw [Fin.forall_fin_two]
  constructor
  · refine ⟨(0 : Fin 1), Finset.mem_sdiff.mpr ⟨broom_all_leaves_blue b 0 (0 : Fin 1), hshort⟩⟩
  · exact sparse_exists_blue_leaf_local _ _ (broom_loss_sparse b loss hcard) 1 hb

theorem broom_single_loss_three (b : ℕ) (hb : 2 ≤ b)
    (loss : Finset (BroomVertex b)) (hcard : loss.card ≤ 1) :
    FinishesBy (broomAdj b) (broomLeaves b \ loss) 3 := by
  classical
  by_cases hshort : broomShortLeaf b ∈ loss
  · let blue := broomLeaves b \ loss
    have hlong : ∀ j : Fin b, broomLongLeaf b j ∈ blue := by
      intro j
      refine Finset.mem_sdiff.mpr ⟨broom_all_leaves_blue b 1 j, ?_⟩
      intro hj
      exact broom_short_ne_long b j (Finset.card_le_one.mp hcard _ hshort _ hj)
    let j : Fin b := ⟨0, by omega⟩
    have hcore1 : Sum.inl (1 : Fin 2) ∈ colorAfter (broomAdj b) blue 1 :=
      core_mem_step_of_blue_leaf (⊤ : SimpleGraph (Fin 2)) (broomLeafCount b) blue 1 j (hlong j)
    have hcore0 : Sum.inl (0 : Fin 2) ∈ colorAfter (broomAdj b) blue 2 := by
      apply (mem_synchronousStep _ _ _).mpr
      refine Or.inr ⟨Sum.inl (1 : Fin 2), hcore1, ?_, ?_⟩
      · exact (by decide : (1 : Fin 2) ≠ 0)
      · intro other ha hw
        cases other with
        | inl i =>
          rcases fin_two_vertex_cases i with rfl | rfl
          · rfl
          · exact False.elim (hw hcore1)
        | inr leaf =>
          rcases leaf with ⟨i, k⟩
          change (1 : Fin 2) = i at ha
          subst i
          exact False.elim (hw (subset_synchronousStep _ _ (hlong k)))
    have hcores : ∀ i : Fin 2, Sum.inl i ∈ colorAfter (broomAdj b) blue 2 := by
      rw [Fin.forall_fin_two]
      exact ⟨hcore0, colorAfter_subset_succ _ blue 1 hcore1⟩
    have hsparse2 : LeafSparse (broomLeafCount b) (colorAfter (broomAdj b) blue 2) :=
      leafSparse_mono _ (broom_loss_sparse b loss hcard)
        (colorAfter_mono_time (broomAdj b) blue (Nat.zero_le 2))
    apply Finset.eq_univ_of_forall
    intro x
    cases x with
    | inl i => exact colorAfter_subset_succ _ blue 2 (hcores i)
    | inr leaf =>
      rcases leaf with ⟨i, k⟩
      exact leaf_mem_step_of_cores_blue (⊤ : SimpleGraph (Fin 2)) (broomLeafCount b)
        _ hsparse2 hcores i k
  · exact FinishesBy_mono_time _ _ (broom_loss_two_of_short_retained b hb loss hcard hshort) (by omega)

theorem broom_short_loss_not_two (b : ℕ) :
    ¬ FinishesBy (broomAdj b) (broomLeaves b \ {broomShortLeaf b}) 2 := by
  classical
  let blue := broomLeaves b \ {broomShortLeaf b}
  have hs0 : broomShortLeaf b ∉ blue := by simp [blue]
  have hc0 : Sum.inl (0 : Fin 2) ∉ blue := by simp [blue, broomLeaves]
  have hs1 : broomShortLeaf b ∉ colorAfter (broomAdj b) blue 1 :=
    corona_leaf_not_step_of_core_white (⊤ : SimpleGraph (Fin 2))
      (broomLeafCount b) blue 0 (0 : Fin 1) hs0 hc0
  have hc1 : Sum.inl (0 : Fin 2) ∉ colorAfter (broomAdj b) blue 1 := by
    intro hm
    rcases (mem_synchronousStep _ _ _).mp hm with hold | ⟨source, hs, ha, _⟩
    · exact hc0 hold
    · cases source with
      | inl i => simp [blue, broomLeaves] at hs
      | inr leaf =>
        rcases leaf with ⟨i, j⟩
        change i = (0 : Fin 2) at ha
        subst i
        have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
        subst j
        exact hs0 hs
  have hs2 : broomShortLeaf b ∉ colorAfter (broomAdj b) blue 2 :=
    corona_leaf_not_step_of_core_white (⊤ : SimpleGraph (Fin 2))
      (broomLeafCount b) (colorAfter (broomAdj b) blue 1) 0 (0 : Fin 1) hs1 hc1
  intro hdone
  change colorAfter (broomAdj b) blue 2 = Finset.univ at hdone
  exact hs2 (by rw [hdone]; exact Finset.mem_univ _)

theorem broom_not_support (b : ℕ) (hb : 2 ≤ b) : ¬ EveryMinimumSupport (broomAdj b) := by
  classical
  intro hU
  let j : Fin b := ⟨0, by omega⟩
  let k : Fin b := ⟨1, by omega⟩
  have hjk : j ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    change (0 : ℕ) = 1 at hv
    exact Nat.zero_ne_one hv
  let support : Finset (BroomVertex b) := {broomLongLeaf b j, broomLongLeaf b k}
  have hleafNe : broomLongLeaf b j ≠ broomLongLeaf b k :=
    fun h => hjk (coronaLeaf_injective (broomLeafCount b) 1 h)
  have hcard : support.card = 2 := by simp [support, hleafNe]
  have hsub : support ⊆ broomLeaves b := by
    intro x hx
    have heq : x = broomLongLeaf b j ∨ x = broomLongLeaf b k := by simpa [support] using hx
    rcases heq with rfl | rfl
    · exact broom_all_leaves_blue b 1 j
    · exact broom_all_leaves_blue b 1 k
  have hforcing : IsForcing (broomAdj b) (broomLeaves b) := by
    refine ⟨3, ?_⟩
    simpa only [Finset.sdiff_empty] using broom_single_loss_three b hb ∅ (by simp)
  have hkill : ¬ IsForcing (broomAdj b) (broomLeaves b \ support) := by
    intro hf
    have hs := leafy_forcing_implies_sparse (⊤ : SimpleGraph (Fin 2)) (broomLeafCount b) _ hf
    exact hjk (hs 1 j k (by simp [support, broomLongLeaf]) (by simp [support, broomLongLeaf]))
  have hminimum : IsMinimumKilling (broomAdj b) (broomLeaves b) support := by
    refine ⟨hsub, hkill, ?_⟩
    intro loss _ hsmall
    refine ⟨3, broom_single_loss_three b hb loss ?_⟩
    rw [hcard] at hsmall
    omega
  have hrestricted : RobustBy (broomAdj b) (broomLeaves b) support 1 2 := by
    intro loss hloss hsize
    apply broom_loss_two_of_short_retained b hb loss hsize
    intro hshort
    have heq : broomShortLeaf b = broomLongLeaf b j ∨
        broomShortLeaf b = broomLongLeaf b k := by simpa [support] using hloss hshort
    exact heq.elim (broom_short_ne_long b j) (broom_short_ne_long b k)
  have hglobal : ¬ RobustBy (broomAdj b) (broomLeaves b) (broomLeaves b) 1 2 := by
    intro hall
    have hs : {broomShortLeaf b} ⊆ broomLeaves b := by
      intro x hx
      have heq := Finset.mem_singleton.mp hx
      subst x
      exact broom_all_leaves_blue b 0 (0 : Fin 1)
    exact broom_short_loss_not_two b (hall {broomShortLeaf b} hs (by simp))
  exact hglobal ((hU (broomLeaves b) hforcing support hminimum 1 2).mpr hrestricted)

theorem doubleStar_one_leaf_not_support (b : ℕ) (hb : 2 ≤ b) :
    ¬ EveryMinimumSupport (doubleStarModel 1 b).Adj := by
  change ¬ EveryMinimumSupport (broomAdj b)
  exact broom_not_support b hb


theorem not_support_of_one_leaf_doubleStar_iso {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (b : ℕ) (hb : 2 ≤ b) (e : G ≃g doubleStarModel 1 b) :
    ¬ EveryMinimumSupport G.Adj := by
  intro h
  exact doubleStar_one_leaf_not_support b hb
    ((EveryMinimumSupport_iso_iff G (doubleStarModel 1 b) e).mp h)

end FaultObservationResearch
