module

/-
Initial coloring for a one-short-arm counterexample.
The construction itself is separate from its time-separation proof.
-/
public import «formalization-path-star-two-empty»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u}

def pathStarFirst (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i) (i : I) : PathStarVertex I L :=
  some ⟨i, ⟨0, by have h := hpos i; omega⟩⟩

def pathStarLast (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i) (i : I) : PathStarVertex I L :=
  some ⟨i, ⟨L i - 1, by have h := hpos i; omega⟩⟩

theorem pathStar_eq_first (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i) (i : I)
    (k : Fin (L i)) (hk : k.val = 0) :
    (some ⟨i, k⟩ : PathStarVertex I L) = pathStarFirst L hpos i := by
  unfold pathStarFirst
  congr 2
  exact Fin.ext hk

theorem pathStar_eq_last (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i) (i : I)
    (k : Fin (L i)) (hk : k.val + 1 = L i) :
    (some ⟨i, k⟩ : PathStarVertex I L) = pathStarLast L hpos i := by
  unfold pathStarLast
  congr 2
  apply Fin.ext
  change k.val = L i - 1
  omega

def pathStarShortSupport (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i) (s a : I) :
    Finset (PathStarVertex I L) := by
  classical
  exact {pathStarFirst L hpos s, pathStarLast L hpos a}

variable [Fintype I] [DecidableEq I]

def pathStarTerminalInitial (L : I → ℕ) (a : I) : Finset (PathStarVertex I L) := by
  classical
  exact Finset.univ.filter (fun v => match v with
    | none => True
    | some ⟨i, k⟩ => (i = a ∧ k.val + 1 = L i) ∨ (i ≠ a ∧ k.val = 0))

omit [DecidableEq I] in
theorem pathStar_terminal_center_mem (L : I → ℕ) (a : I) :
    none ∈ pathStarTerminalInitial L a := by
  classical
  simp [pathStarTerminalInitial]

omit [DecidableEq I] in
theorem pathStar_terminal_head_mem (L : I → ℕ) (a i : I) (hia : i ≠ a)
    (k : Fin (L i)) (hk : k.val = 0) :
    some ⟨i, k⟩ ∈ pathStarTerminalInitial L a := by
  classical
  simp [pathStarTerminalInitial, hia, hk]

omit [DecidableEq I] in
theorem pathStar_terminal_end_mem (L : I → ℕ) (a : I)
    (k : Fin (L a)) (hk : k.val + 1 = L a) :
    some ⟨a, k⟩ ∈ pathStarTerminalInitial L a := by
  classical
  simp [pathStarTerminalInitial, hk]

omit [DecidableEq I] in
theorem pathStar_terminal_arm_mem_iff (L : I → ℕ) (a : I) (k : Fin (L a)) :
    some ⟨a, k⟩ ∈ pathStarTerminalInitial L a ↔ k.val + 1 = L a := by
  classical
  simp [pathStarTerminalInitial]

omit [DecidableEq I] in
theorem pathStar_terminal_other_mem_iff (L : I → ℕ) (a i : I) (hia : i ≠ a)
    (k : Fin (L i)) :
    some ⟨i, k⟩ ∈ pathStarTerminalInitial L a ↔ k.val = 0 := by
  classical
  simp [pathStarTerminalInitial, hia]

omit [Fintype I] [DecidableEq I] in
theorem pathStar_short_support_card (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (s a : I) (hsa : s ≠ a) : (pathStarShortSupport L hpos s a).card = 2 := by
  classical
  have hne : pathStarFirst L hpos s ≠ pathStarLast L hpos a := by
    intro heq
    exact hsa (pathStar_nodes_eq_arm L s a _ _ heq)
  simp [pathStarShortSupport, hne]

omit [DecidableEq I] in
theorem pathStar_short_support_subset (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (s a : I) (hsa : s ≠ a) : pathStarShortSupport L hpos s a ⊆ pathStarTerminalInitial L a := by
  classical
  intro v hv
  rcases (by simpa [pathStarShortSupport] using hv :
    v = pathStarFirst L hpos s ∨ v = pathStarLast L hpos a) with rfl | rfl
  · exact pathStar_terminal_head_mem L a s hsa _ rfl
  · apply pathStar_terminal_end_mem
    change L a - 1 + 1 = L a
    have h := hpos a
    omega

theorem pathStar_short_support_kills (L : I → ℕ) (hpos : ∀ i, 1 ≤ L i)
    (s a : I) (hsa : s ≠ a) :
    ¬ IsForcing (pathStarGraph L).Adj
      (pathStarTerminalInitial L a \ pathStarShortSupport L hpos s a) := by
  classical
  apply pathStar_two_empty_arms_not_forcing L s a hsa
    (by have h := hpos s; omega) (by have h := hpos a; omega)
  · intro k hk
    obtain ⟨hinitial, hnot⟩ := Finset.mem_sdiff.mp hk
    have hzero := (pathStar_terminal_other_mem_iff L a s hsa k).mp hinitial
    apply hnot
    rw [pathStar_eq_first L hpos s k hzero]
    simp [pathStarShortSupport]
  · intro k hk
    obtain ⟨hinitial, hnot⟩ := Finset.mem_sdiff.mp hk
    have hend := (pathStar_terminal_arm_mem_iff L a k).mp hinitial
    apply hnot
    rw [pathStar_eq_last L hpos a k hend]
    simp [pathStarShortSupport]

end FaultObservationResearch
