module

/-
Two nonempty arms with no initial blue vertex block each other permanently.
This static process lemma is not a claim of mathematical originality.
-/
public import «formalization-single-branch-realization»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem pathStar_nodes_eq_arm (L : I → ℕ) (a b : I) (k : Fin (L a)) (l : Fin (L b))
    (heq : (some ⟨a, k⟩ : PathStarVertex I L) = some ⟨b, l⟩) : a = b := by
  exact congrArg (fun z : Σ i : I, Fin (L i) => z.1) (Option.some.inj heq)

theorem pathStar_empty_arm_step (L : I → ℕ) (a b : I) (hab : a ≠ b)
    (hpos : 0 < L b) (C : Finset (PathStarVertex I L))
    (ha : ∀ k : Fin (L a), (some ⟨a, k⟩ : PathStarVertex I L) ∉ C)
    (hb : ∀ k : Fin (L b), (some ⟨b, k⟩ : PathStarVertex I L) ∉ C) :
    ∀ k : Fin (L a), (some ⟨a, k⟩ : PathStarVertex I L) ∉
      synchronousStep (pathStarGraph L).Adj C := by
  classical
  intro k hk
  rcases (mem_synchronousStep _ _ _).mp hk with hold | ⟨source, hs, hadj, hu⟩
  · exact ha k hold
  · cases source with
    | none =>
      let head : Fin (L b) := ⟨0, hpos⟩
      have hneighbor : (pathStarGraph L).Adj none (some ⟨b, head⟩) := by
        change head.val = 0
        rfl
      have heq := hu (some ⟨b, head⟩) hneighbor (hb head)
      exact hab (pathStar_nodes_eq_arm L b a head k heq).symm
    | some source =>
      obtain ⟨i, l⟩ := source
      change i = a ∧ (l.val + 1 = k.val ∨ k.val + 1 = l.val) at hadj
      obtain ⟨rfl, _⟩ := hadj
      exact ha l hs

theorem pathStar_two_empty_arms_white (L : I → ℕ) (a b : I) (hab : a ≠ b)
    (hapos : 0 < L a) (hbpos : 0 < L b) (C : Finset (PathStarVertex I L))
    (ha : ∀ k : Fin (L a), (some ⟨a, k⟩ : PathStarVertex I L) ∉ C)
    (hb : ∀ k : Fin (L b), (some ⟨b, k⟩ : PathStarVertex I L) ∉ C) (t : ℕ) :
    (∀ k : Fin (L a), (some ⟨a, k⟩ : PathStarVertex I L) ∉
      colorAfter (pathStarGraph L).Adj C t) ∧
    (∀ k : Fin (L b), (some ⟨b, k⟩ : PathStarVertex I L) ∉
      colorAfter (pathStarGraph L).Adj C t) := by
  induction t with
  | zero => exact ⟨ha, hb⟩
  | succ t ih =>
    exact ⟨pathStar_empty_arm_step L a b hab hbpos _ ih.1 ih.2,
      pathStar_empty_arm_step L b a hab.symm hapos _ ih.2 ih.1⟩

theorem pathStar_two_empty_arms_not_forcing (L : I → ℕ) (a b : I) (hab : a ≠ b)
    (hapos : 0 < L a) (hbpos : 0 < L b) (C : Finset (PathStarVertex I L))
    (ha : ∀ k : Fin (L a), (some ⟨a, k⟩ : PathStarVertex I L) ∉ C)
    (hb : ∀ k : Fin (L b), (some ⟨b, k⟩ : PathStarVertex I L) ∉ C) :
    ¬ IsForcing (pathStarGraph L).Adj C := by
  rintro ⟨t, ht⟩
  have hwhite := (pathStar_two_empty_arms_white L a b hab hapos hbpos C ha hb t).1
  let head : Fin (L a) := ⟨0, hapos⟩
  apply hwhite head
  rw [ht]
  exact Finset.mem_univ _

end FaultObservationResearch
