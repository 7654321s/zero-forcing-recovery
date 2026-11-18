module

/-
Local recovery steps on a path star: an intact head-second pair restores the center,
and a blue center restores a head when all other heads are blue.
-/
public import «formalization-single-branch-realization»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem pathStar_center_from_intact_pair (lengths : I → ℕ) (i : I)
    (head second : Fin (lengths i)) (hheadval : head.val = 0)
    (hsecondval : second.val = 1) (C : Finset (PathStarVertex I lengths))
    (hhead : some ⟨i, head⟩ ∈ C) (hsecond : some ⟨i, second⟩ ∈ C) :
    none ∈ colorAfter (pathStarGraph lengths).Adj C 1 := by
  classical
  apply (mem_synchronousStep _ C none).mpr
  refine Or.inr ⟨some ⟨i, head⟩, hhead, hheadval, ?_⟩
  intro other hadj hwhite
  cases other with
  | none => rfl
  | some other =>
    obtain ⟨j, k⟩ := other
    change i = j ∧ (head.val + 1 = k.val ∨ k.val + 1 = head.val) at hadj
    obtain ⟨rfl, hleft | hright⟩ := hadj
    · have hk : k = second := Fin.ext (by omega)
      subst k
      exact False.elim (hwhite hsecond)
    · omega

theorem pathStar_missing_head_recovers (lengths : I → ℕ) (i : I)
    (head : Fin (lengths i)) (hheadval : head.val = 0)
    (C : Finset (PathStarVertex I lengths)) (s : ℕ)
    (hcenter : none ∈ colorAfter (pathStarGraph lengths).Adj C s)
    (hothers : ∀ (j : I), j ≠ i → ∀ k : Fin (lengths j), k.val = 0 →
      some ⟨j, k⟩ ∈ colorAfter (pathStarGraph lengths).Adj C s) :
    some ⟨i, head⟩ ∈ colorAfter (pathStarGraph lengths).Adj C (s + 1) := by
  classical
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨none, hcenter, hheadval, ?_⟩
  intro other hadj hwhite
  cases other with
  | none => exact hadj.elim
  | some other =>
    obtain ⟨j, k⟩ := other
    change k.val = 0 at hadj
    by_cases hji : j = i
    · subst j
      have hk : k = head := Fin.ext (hadj.trans hheadval.symm)
      exact congrArg (fun k : Fin (lengths i) =>
        (some ⟨i, k⟩ : PathStarVertex I lengths)) hk
    · exact False.elim (hwhite (hothers j hji k hadj))

end FaultObservationResearch
