module

/-
Endpoint-to-center propagation for a single arm of a path-star.
This auxiliary lemma does not settle the one-short-arm obstruction.
-/
public import «formalization-single-branch-realization»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem pathStar_arm_suffix_blue (L : I → ℕ) (i : I)
    (C : Finset (PathStarVertex I L))
    (hend : ∀ k : Fin (L i), k.val + 1 = L i → some ⟨i, k⟩ ∈ C)
    (t : ℕ) : ∀ k : Fin (L i), L i ≤ k.val + t + 1 →
      some ⟨i, k⟩ ∈ colorAfter (pathStarGraph L).Adj C t := by
  classical
  let G := pathStarGraph L
  induction t with
  | zero =>
    intro k hk
    exact hend k (by have h := k.isLt; omega)
  | succ t ih =>
    intro k hk
    by_cases hold : L i ≤ k.val + t + 1
    · exact colorAfter_subset_succ G.Adj C t (ih k hold)
    · have hstep : k.val + 1 < L i := by omega
      let previous : Fin (L i) := ⟨k.val + 1, hstep⟩
      have hp : L i ≤ previous.val + t + 1 := by
        change L i ≤ k.val + 1 + t + 1
        omega
      apply (mem_synchronousStep G.Adj (colorAfter G.Adj C t) _).mpr
      refine Or.inr ⟨some ⟨i, previous⟩, ih previous hp, ?_, ?_⟩
      · change i = i ∧ (previous.val + 1 = k.val ∨ k.val + 1 = previous.val)
        exact ⟨rfl, Or.inr rfl⟩
      · intro other hadj hwhite
        cases other with
        | none =>
          change previous.val = 0 at hadj
          change k.val + 1 = 0 at hadj
          omega
        | some other =>
          obtain ⟨j, l⟩ := other
          change i = j ∧ (previous.val + 1 = l.val ∨ l.val + 1 = previous.val) at hadj
          obtain ⟨rfl, hright | hleft⟩ := hadj
          · have hl : L i ≤ l.val + t + 1 := by
              change k.val + 1 + 1 = l.val at hright
              change L i ≤ k.val + 1 + t + 1 at hp
              omega
            exact False.elim (hwhite (ih l hl))
          · have hl : l = k := Fin.ext (by
              change l.val + 1 = k.val + 1 at hleft
              omega)
            exact congrArg (fun z : Fin (L i) =>
              (some ⟨i, z⟩ : PathStarVertex I L)) hl

theorem pathStar_arm_endpoint_finishes (L : I → ℕ) (i : I)
    (C : Finset (PathStarVertex I L))
    (hend : ∀ k : Fin (L i), k.val + 1 = L i → some ⟨i, k⟩ ∈ C) :
    ∀ k : Fin (L i), some ⟨i, k⟩ ∈ colorAfter (pathStarGraph L).Adj C (L i - 1) := by
  intro k
  apply pathStar_arm_suffix_blue L i C hend (L i - 1) k
  have h := k.isLt
  omega

end FaultObservationResearch
