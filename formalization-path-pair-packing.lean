module

/-
A standard greedy edge packing and equal-size vertex cover on a path subset.
Endpoint singleton forcing cells are still to be joined separately.
This is a proof component, not an originality or full time-support claim.
-/
public import «formalization-path-gap»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

def PathCellBefore (n : ℕ) (A B : Finset (Fin (n + 1))) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, x.val < y.val

structure PathPairCoverPacking (n : ℕ) (blue : Finset (Fin (n + 1)))
    (units : List (Finset (Fin (n + 1)))) (cover : Finset (Fin (n + 1))) : Prop where
  pairs : ∀ cell ∈ units, ∃ u ∈ blue, ∃ v ∈ blue, u.val + 1 = v.val ∧ cell = {u, v}
  ordered : units.Pairwise (PathCellBefore n)
  cover_subset : cover ⊆ blue
  card_eq : cover.card = units.length
  covers : ∀ u ∈ blue, ∀ v ∈ blue, u.val + 1 = v.val → u ∈ cover ∨ v ∈ cover

theorem pathCellBefore_disjoint (n : ℕ) (A B : Finset (Fin (n + 1)))
    (hbefore : PathCellBefore n A B) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  exact Nat.lt_irrefl x.val (hbefore x hxA x hxB)

theorem pathPairCoverPacking_cell_subset (n : ℕ) (blue : Finset (Fin (n + 1)))
    (units : List (Finset (Fin (n + 1)))) (cover : Finset (Fin (n + 1)))
    (hpack : PathPairCoverPacking n blue units cover)
    (cell : Finset (Fin (n + 1))) (hcell : cell ∈ units) : cell ⊆ blue := by
  classical
  obtain ⟨u, hu, v, hv, _, heq⟩ := hpack.pairs cell hcell
  rw [heq]
  intro x hx
  rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx) with hx | hx
  · rwa [hx]
  · rwa [hx]

theorem exists_path_pair_cover_packing (n : ℕ) (blue : Finset (Fin (n + 1))) :
    ∃ units : List (Finset (Fin (n + 1))), ∃ cover : Finset (Fin (n + 1)),
      PathPairCoverPacking n blue units cover := by
  classical
  have general : ∀ m : ℕ, ∀ S : Finset (Fin (n + 1)), S.card = m →
      ∃ units : List (Finset (Fin (n + 1))), ∃ cover : Finset (Fin (n + 1)),
        PathPairCoverPacking n S units cover := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro S hcard
      by_cases hempty : S = ∅
      · subst S
        refine ⟨[], ∅, ?_⟩
        constructor <;> simp
      · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        let u := S.min' hne
        have hu : u ∈ S := S.min'_mem hne
        have hmin : ∀ x ∈ S, u.val ≤ x.val := fun x hx => S.min'_le x hx
        by_cases hnext : ∃ v ∈ S, u.val + 1 = v.val
        · obtain ⟨v, hv, huv⟩ := hnext
          have huvNe : u ≠ v := by
            intro heq
            have heqVal := congrArg Fin.val heq
            omega
          have hvErase : v ∈ S.erase u := Finset.mem_erase.mpr ⟨Ne.symm huvNe, hv⟩
          have hsize : 2 ≤ S.card := by
            have hp : 0 < (S.erase u).card := Finset.card_pos.mpr ⟨v, hvErase⟩
            rw [Finset.card_erase_of_mem hu] at hp
            omega
          let R := (S.erase u).erase v
          have hRsub : R ⊆ S := by
            intro x hx
            exact (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
          have hRcard : R.card + 2 = S.card := by
            dsimp [R]
            rw [Finset.card_erase_of_mem hvErase, Finset.card_erase_of_mem hu]
            omega
          obtain ⟨units, cover, hpack⟩ := ih R.card (by omega) R rfl
          have hAfter : ∀ y ∈ R, v.val < y.val := by
            intro y hy
            have hyS := hRsub hy
            have hyNeV := (Finset.mem_erase.mp hy).1
            have hyNeU := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
            have hyValNeV : y.val ≠ v.val := fun h => hyNeV (Fin.ext h)
            have hyValNeU : y.val ≠ u.val := fun h => hyNeU (Fin.ext h)
            have hle := hmin y hyS
            omega
          have hvNotCover : v ∉ cover := by
            intro hvc
            have hvR := hpack.cover_subset hvc
            exact (Finset.mem_erase.mp hvR).1 rfl
          refine ⟨{u, v} :: units, insert v cover, ?_⟩
          constructor
          · intro cell hcell
            rcases List.mem_cons.mp hcell with heq | hrest
            · subst cell
              exact ⟨u, hu, v, hv, huv, rfl⟩
            · obtain ⟨a, ha, b, hb, hab, heq⟩ := hpack.pairs cell hrest
              exact ⟨a, hRsub ha, b, hRsub hb, hab, heq⟩
          · apply List.pairwise_cons.mpr
            refine ⟨?_, hpack.ordered⟩
            intro cell hcell x hx y hy
            have hyR := pathPairCoverPacking_cell_subset n R units cover hpack cell hcell hy
            have hyv := hAfter y hyR
            rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx) with hx | hx
            · rw [hx]
              omega
            · rw [hx]
              exact hyv
          · intro x hx
            rcases Finset.mem_insert.mp hx with heq | hc
            · rw [heq]
              exact hv
            · exact hRsub (hpack.cover_subset hc)
          · simp only [Finset.card_insert_of_notMem hvNotCover, hpack.card_eq, List.length_cons]
          · intro a ha b hb hab
            by_cases haV : a = v
            · exact Or.inl (Finset.mem_insert.mpr (Or.inl haV))
            by_cases hbV : b = v
            · exact Or.inr (Finset.mem_insert.mpr (Or.inl hbV))
            have haU : a ≠ u := by
              intro heq
              have hbVal : b.val = v.val := by rw [heq] at hab; omega
              exact hbV (Fin.ext hbVal)
            have hbU : b ≠ u := by
              intro heq
              have hle := hmin a ha
              have heqVal := congrArg Fin.val heq
              omega
            have haR : a ∈ R := Finset.mem_erase.mpr ⟨haV, Finset.mem_erase.mpr ⟨haU, ha⟩⟩
            have hbR : b ∈ R := Finset.mem_erase.mpr ⟨hbV, Finset.mem_erase.mpr ⟨hbU, hb⟩⟩
            exact (hpack.covers a haR b hbR hab).elim
              (fun h => Or.inl (Finset.mem_insert.mpr (Or.inr h)))
              (fun h => Or.inr (Finset.mem_insert.mpr (Or.inr h)))
        · let R := S.erase u
          have hRsub : R ⊆ S := fun _ hx => (Finset.mem_erase.mp hx).2
          have hRcard : R.card + 1 = S.card := by
            dsimp [R]
            rw [Finset.card_erase_of_mem hu]
            have hp := Finset.card_pos.mpr hne
            omega
          obtain ⟨units, cover, hpack⟩ := ih R.card (by omega) R rfl
          refine ⟨units, cover, ?_⟩
          constructor
          · intro cell hcell
            obtain ⟨a, ha, b, hb, hab, heq⟩ := hpack.pairs cell hcell
            exact ⟨a, hRsub ha, b, hRsub hb, hab, heq⟩
          · exact hpack.ordered
          · exact fun _ hx => hRsub (hpack.cover_subset hx)
          · exact hpack.card_eq
          · intro a ha b hb hab
            have haU : a ≠ u := by
              intro heq
              exact hnext ⟨b, hb, by rwa [heq] at hab⟩
            have hbU : b ≠ u := by
              intro heq
              have hle := hmin a ha
              have heqVal := congrArg Fin.val heq
              omega
            exact hpack.covers a (Finset.mem_erase.mpr ⟨haU, ha⟩)
              b (Finset.mem_erase.mpr ⟨hbU, hb⟩) hab
  exact general blue.card blue rfl

end FaultObservationResearch
