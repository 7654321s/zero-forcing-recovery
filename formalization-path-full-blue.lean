module

/-
The full-initial-blue case of the path time-support theorem.
The general arbitrary-initial-blue path theorem remains a separate target.
These are components of the current proof, not a novelty claim.
-/
public import «formalization-path-forcing»
public import Mathlib.Data.Finset.Max
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

def PathPrefix (n : ℕ) (part whole : Finset (Fin (n + 1))) : Prop :=
  part ⊆ whole ∧ ∀ x ∈ part, ∀ y ∈ whole, y.val ≤ x.val → y ∈ part

theorem pathPrefix_self (n : ℕ) (whole : Finset (Fin (n + 1))) :
    PathPrefix n whole whole := ⟨fun _ h => h, fun _ _ _ hy _ => hy⟩

theorem pathPrefix_trans (n : ℕ) (A B C : Finset (Fin (n + 1)))
    (hAB : PathPrefix n A B) (hBC : PathPrefix n B C) : PathPrefix n A C := by
  refine ⟨fun _ hx => hBC.1 (hAB.1 hx), ?_⟩
  intro x hx y hy hle
  exact hAB.2 x hx y (hBC.2 x (hAB.1 hx) y hy hle) hle

theorem pathPrefix_erase_max (n : ℕ) (whole : Finset (Fin (n + 1))) (hne : whole.Nonempty) :
    PathPrefix n (whole.erase (whole.max' hne)) whole := by
  classical
  refine ⟨fun _ hx => (Finset.mem_erase.mp hx).2, ?_⟩
  intro x hx y hy hle
  have hxH := (Finset.mem_erase.mp hx).2
  have hxNe := (Finset.mem_erase.mp hx).1
  refine Finset.mem_erase.mpr ⟨?_, hy⟩
  intro heq
  have hxMax : x ≤ whole.max' hne := whole.le_max' x hxH
  have hMaxX : whole.max' hne ≤ x := by
    rw [← heq]
    exact hle
  exact hxNe (le_antisymm hxMax hMaxX)

theorem exists_pathPrefix_card (n : ℕ) (whole : Finset (Fin (n + 1)))
    (k : ℕ) (hk : k ≤ whole.card) :
    ∃ part : Finset (Fin (n + 1)), PathPrefix n part whole ∧ part.card = k := by
  classical
  have general : ∀ m : ℕ, ∀ H : Finset (Fin (n + 1)), H.card = m →
      ∀ k : ℕ, k ≤ m → ∃ E : Finset (Fin (n + 1)), PathPrefix n E H ∧ E.card = k := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro H hcard k hk
      by_cases hsame : k = m
      · exact ⟨H, pathPrefix_self n H, hcard.trans hsame.symm⟩
      · have hne : H.Nonempty := Finset.card_pos.mp (by omega)
        let S := H.erase (H.max' hne)
        have hS : S.card + 1 = m := by
          dsimp [S]
          rw [Finset.card_erase_of_mem (H.max'_mem hne)]
          omega
        have hlt : S.card < m := by omega
        have hkS : k ≤ S.card := by omega
        obtain ⟨E, hES, hE⟩ := ih S.card hlt S rfl k hkS
        exact ⟨E, pathPrefix_trans n E S H hES (pathPrefix_erase_max n H hne), hE⟩
  exact general whole.card whole rfl k hk

theorem pathPrefix_last_not_mem (n : ℕ) (part whole : Finset (Fin (n + 1)))
    (hprefix : PathPrefix n part whole) (hproper : part.card < whole.card) :
    Fin.last n ∉ part := by
  intro hl
  have hsub : whole ⊆ part := by
    intro x hx
    apply hprefix.2 (Fin.last n) hl x hx
    change x.val ≤ n
    have := x.isLt
    omega
  have hc := Finset.card_le_card hsub
  omega

theorem path_max_loss_mem_step (n : ℕ) (loss : Finset (Fin (n + 1)))
    (hne : loss.Nonempty) (hlast : Fin.last n ∉ loss) :
    loss.max' hne ∈ synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ loss) := by
  classical
  let m := loss.max' hne
  have hm : m ∈ loss := loss.max'_mem hne
  have hmn : m.val < n := by
    have hneval : m.val ≠ n := by
      intro h
      have heq : m = Fin.last n := Fin.ext h
      exact hlast (by rwa [← heq])
    have := m.isLt
    omega
  let source : Fin (n + 1) := ⟨m.val + 1, by omega⟩
  have hsNot : source ∉ loss := by
    intro hs
    have hle : source.val ≤ m.val := loss.le_max' source hs
    change m.val + 1 ≤ m.val at hle
    omega
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨source, by simp [hsNot], SimpleGraph.pathGraph_adj.mpr (Or.inr rfl), ?_⟩
  intro other ha hw
  have ho : other ∈ loss := by simpa using hw
  have hle : other.val ≤ m.val := loss.le_max' other ho
  rcases SimpleGraph.pathGraph_adj.mp ha with hright | hleft
  · change m.val + 1 + 1 = other.val at hright
    omega
  · apply Fin.ext
    change other.val + 1 = m.val + 1 at hleft
    omega

theorem path_prefix_step_subset (n : ℕ) (part whole : Finset (Fin (n + 1)))
    (hcover : HitsPathSeeds n Finset.univ whole) (hprefix : PathPrefix n part whole)
    (hne : part.Nonempty) :
    synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ part) ⊆
      (Finset.univ \ part) ∪ {part.max' hne} := by
  classical
  let m := part.max' hne
  have hm : m ∈ part := part.max'_mem hne
  intro target ht
  by_cases hold : target ∈ Finset.univ \ part
  · exact Finset.mem_union.mpr (Or.inl hold)
  have htP : target ∈ part := by simpa using hold
  have htLe : target.val ≤ m.val := part.le_max' target htP
  rcases (mem_synchronousStep _ _ _).mp ht with h | ⟨source, hs, ha, hu⟩
  · exact False.elim (hold h)
  · have hsNot : source ∉ part := (Finset.mem_sdiff.mp hs).2
    by_cases hright : m.val < source.val
    · have heq : target = m := by
        apply Fin.ext
        rcases SimpleGraph.pathGraph_adj.mp ha with ha | ha <;> omega
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr heq))
    · have hsLe : source.val ≤ m.val := by omega
      have hsNotH : source ∉ whole :=
        fun h => hsNot (hprefix.2 m hm source h hsLe)
      have hs0 : source.val ≠ 0 := by
        intro h
        have heq : source = 0 := Fin.ext h
        exact hsNotH (by rw [heq]; exact hcover.1 (Finset.mem_univ _))
      have hsn : source.val ≠ n := by
        intro h
        have heq : source = Fin.last n := Fin.ext h
        exact hsNotH (by rw [heq]; exact hcover.2.1 (Finset.mem_univ _))
      have hsNeM : source.val ≠ m.val := by
        intro h
        have heq : source = m := Fin.ext h
        exact hsNot (by rwa [heq])
      let left : Fin (n + 1) := ⟨source.val - 1, by have := source.isLt; omega⟩
      let right : Fin (n + 1) := ⟨source.val + 1, by have := source.isLt; omega⟩
      have hleftEq : left.val + 1 = source.val := by dsimp [left]; omega
      have hleftH : left ∈ whole := by
        have h := hcover.2.2 left source (Finset.mem_univ _) (Finset.mem_univ _) hleftEq
        exact h.elim (fun h => h) (fun h => False.elim (hsNotH h))
      have hrightH : right ∈ whole := by
        have h := hcover.2.2 source right (Finset.mem_univ _) (Finset.mem_univ _) rfl
        exact h.elim (fun h => False.elim (hsNotH h)) (fun h => h)
      have hleftP : left ∈ part := hprefix.2 m hm left hleftH (by dsimp [left]; omega)
      have hrightP : right ∈ part := hprefix.2 m hm right hrightH (by dsimp [right]; omega)
      have hL := hu left (SimpleGraph.pathGraph_adj.mpr (Or.inr hleftEq)) (by simp [hleftP])
      have hR := hu right (SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)) (by simp [hrightP])
      have hv := congrArg Fin.val (hL.trans hR.symm)
      change source.val - 1 = source.val + 1 at hv
      omega

theorem path_prefix_step (n : ℕ) (part whole : Finset (Fin (n + 1)))
    (hcover : HitsPathSeeds n Finset.univ whole) (hprefix : PathPrefix n part whole)
    (hne : part.Nonempty) (hproper : part.card < whole.card) :
    synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ part) =
      Finset.univ \ part.erase (part.max' hne) := by
  classical
  have hmax := path_max_loss_mem_step n part hne (pathPrefix_last_not_mem n part whole hprefix hproper)
  have hstep : synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ part) =
      (Finset.univ \ part) ∪ {part.max' hne} := by
    apply le_antisymm (path_prefix_step_subset n part whole hcover hprefix hne)
    intro x hx
    rcases Finset.mem_union.mp hx with hold | hsingle
    · exact subset_synchronousStep _ _ hold
    · have heq := Finset.mem_singleton.mp hsingle
      simpa only [heq] using hmax
  rw [hstep]
  ext x
  by_cases hx : x = part.max' hne
  · subst x
    simp
  · simp [hx]

theorem path_prefix_finishes_iff (n : ℕ) (part whole : Finset (Fin (n + 1)))
    (hcover : HitsPathSeeds n Finset.univ whole) (hprefix : PathPrefix n part whole)
    (hproper : part.card < whole.card) (deadline : ℕ) :
    FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ part) deadline ↔
      part.card ≤ deadline := by
  classical
  have general : ∀ m : ℕ, ∀ E : Finset (Fin (n + 1)), E.card = m →
      PathPrefix n E whole → E.card < whole.card → ∀ t : ℕ,
      FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ E) t ↔ E.card ≤ t := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro E hcard hp hlt t
      by_cases hempty : E = ∅
      · subst E
        simp [FinishesBy]
      · have hne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        have hm : E.max' hne ∈ E := E.max'_mem hne
        have hpos : 0 < E.card := Finset.card_pos.mpr hne
        cases t with
        | zero =>
          constructor
          · intro hf
            have hx : E.max' hne ∈ Finset.univ \ E := by
              change Finset.univ \ E = Finset.univ at hf
              rw [hf]
              exact Finset.mem_univ _
            exact False.elim ((Finset.mem_sdiff.mp hx).2 hm)
          · intro hc
            omega
        | succ t =>
          let S := E.erase (E.max' hne)
          have hs : S.card + 1 = E.card := by
            dsimp [S]
            rw [Finset.card_erase_of_mem hm]
            omega
          have hsp : PathPrefix n S whole :=
            pathPrefix_trans n S E whole (pathPrefix_erase_max n E hne) hp
          have hshift := colorAfter_add (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ E) 1 t
          change colorAfter _ _ (1 + t) = colorAfter _ (synchronousStep _ (Finset.univ \ E)) t at hshift
          rw [Nat.add_comm 1 t, path_prefix_step n E whole hcover hp hne hlt] at hshift
          change colorAfter _ _ (t + 1) = Finset.univ ↔ E.card ≤ t + 1
          rw [hshift]
          change FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ S) t ↔ E.card ≤ t + 1
          rw [ih S.card (by omega) S rfl hsp (by omega) t]
          omega
  exact general part.card part rfl hprefix hproper deadline

theorem path_full_blue_restricted_robust_iff (n : ℕ) (support : Finset (Fin (n + 1)))
    (hminimum : IsMinimumKilling (SimpleGraph.pathGraph (n + 1)).Adj Finset.univ support)
    (budget deadline : ℕ) :
    RobustBy (SimpleGraph.pathGraph (n + 1)).Adj Finset.univ support budget deadline ↔
      budget < support.card ∧ budget ≤ deadline := by
  classical
  constructor
  · intro hr
    have hsmall : budget < support.card := by
      by_contra hlarge
      have hc : support.card ≤ budget := by omega
      exact hminimum.2.1 ⟨deadline, hr support (fun _ hx => hx) hc⟩
    obtain ⟨part, hp, hcard⟩ := exists_pathPrefix_card n support budget (Nat.le_of_lt hsmall)
    have hcover := (path_nonforcing_sdiff_iff_hits_seeds n Finset.univ support).mp hminimum.2.1
    have hf := hr part hp.1 (Nat.le_of_eq hcard)
    have hbound := (path_prefix_finishes_iff n part support hcover hp (by omega) deadline).mp hf
    exact ⟨hsmall, by omega⟩
  · rintro ⟨hsmall, htime⟩ loss hsub hc
    exact FinishesBy_mono_time _ _
      (full_blue_robust_by_budget _ support hminimum budget hsmall loss
        (fun _ hx => hminimum.1 (hsub hx)) hc) htime

theorem path_full_blue_robust_iff (n : ℕ) (support : Finset (Fin (n + 1)))
    (hminimum : IsMinimumKilling (SimpleGraph.pathGraph (n + 1)).Adj Finset.univ support)
    (budget deadline : ℕ) :
    RobustBy (SimpleGraph.pathGraph (n + 1)).Adj Finset.univ Finset.univ budget deadline ↔
      budget < support.card ∧ budget ≤ deadline := by
  constructor
  · intro hr
    apply (path_full_blue_restricted_robust_iff n support hminimum budget deadline).mp
    intro loss hsub hc
    exact hr loss (fun _ hx => hminimum.1 (hsub hx)) hc
  · rintro ⟨hsmall, htime⟩ loss hsub hc
    exact FinishesBy_mono_time _ _
      (full_blue_robust_by_budget _ support hminimum budget hsmall loss hsub hc) htime

theorem path_full_blue_support (n : ℕ) (support : Finset (Fin (n + 1)))
    (hminimum : IsMinimumKilling (SimpleGraph.pathGraph (n + 1)).Adj Finset.univ support)
    (budget deadline : ℕ) :
    RobustBy (SimpleGraph.pathGraph (n + 1)).Adj Finset.univ Finset.univ budget deadline ↔
      RobustBy (SimpleGraph.pathGraph (n + 1)).Adj Finset.univ support budget deadline := by
  rw [path_full_blue_robust_iff n support hminimum,
    path_full_blue_restricted_robust_iff n support hminimum]

end FaultObservationResearch
