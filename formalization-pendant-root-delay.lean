module

/-
An empty pendant arm cannot start until its initially white root turns blue.
Auxiliary speed bounds for the remaining equal-arm cases; not a classification.
-/
public import «formalization-two-pendant-clock»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem twoPendant_empty_A_white_root_speed (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hroot : twoPendantCore V a b root ∉ C)
    (hA : ∀ i, twoPendantA V a b i ∉ C) (t : ℕ) :
    ∀ i, twoPendantA V a b i ∈ colorAfter (twoPendantGraph R root a b).Adj C t →
      i.val + 2 ≤ t := by
  classical
  let G := twoPendantGraph R root a b
  induction t with
  | zero =>
    intro i hi
    exact False.elim (hA i hi)
  | succ t ih =>
    intro i hi
    rcases (mem_synchronousStep G.Adj (colorAfter G.Adj C t) _).mp hi with
      hold | ⟨source, hs, ha, _⟩
    · have hb := ih i hold
      omega
    · rcases source with x | (j | k)
      · change x = root ∧ i = 0 at ha
        rcases ha with ⟨rfl, rfl⟩
        have ht : 1 ≤ t := by
          by_contra h
          have ht0 : t = 0 := by omega
          subst t
          exact hroot hs
        change 0 + 2 ≤ t + 1
        omega
      · have hb := ih j hs
        rcases SimpleGraph.pathGraph_adj.mp ha with hadj | hadj <;> omega
      · exact ha.elim

theorem twoPendant_empty_A_white_root_completion_lower
    (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hroot : twoPendantCore V a b root ∉ C)
    (hA : ∀ i, twoPendantA V a b i ∉ C) (t : ℕ)
    (hfinish : FinishesBy (twoPendantGraph R root a b).Adj C t) : a + 2 ≤ t := by
  have hm : twoPendantA V a b (Fin.last a) ∈
      colorAfter (twoPendantGraph R root a b).Adj C t := by
    rw [hfinish]
    exact Finset.mem_univ _
  exact twoPendant_empty_A_white_root_speed R root a b C hroot hA t (Fin.last a) hm

end FaultObservationResearch
