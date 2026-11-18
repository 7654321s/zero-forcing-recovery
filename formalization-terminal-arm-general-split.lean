module

/-
Extend the terminal-length split to every sorted positive length list.
This is arithmetic only. Existence of such a decomposition for an arbitrary
tree, its graph isomorphism, and research priority are separate obligations.
-/
public import «formalization-terminal-arm-comparison»

@[expose] public section

set_option autoImplicit false
namespace FaultObservationResearch

theorem terminal_arm_sum_eq_one_iff (k : ℕ) (lengths : Fin (k + 2) → ℕ)
    (hmono : Monotone lengths) (hpos : ∀ i, 1 ≤ lengths i) :
    terminalArmSum k lengths = 1 ↔ ∀ i, lengths i = 1 := by
  constructor
  · intro heq i
    have hlastPos := hpos (Fin.last (k + 1))
    have hprevPos := hpos (armPenultimateIndex k)
    have hlast : lengths (Fin.last (k + 1)) = 1 := by
      dsimp [terminalArmSum] at heq
      omega
    have hi : lengths i ≤ lengths (Fin.last (k + 1)) := hmono (Fin.le_last i)
    have hipos := hpos i
    omega
  · intro hone
    dsimp [terminalArmSum]
    rw [hone, hone]

theorem terminal_arm_all_positive_cases
    (ku kv : ℕ) (left : Fin (ku + 2) → ℕ) (right : Fin (kv + 2) → ℕ)
    (hleft : Monotone left) (hright : Monotone right)
    (hleftPos : ∀ i, 1 ≤ left i) (hrightPos : ∀ i, 1 ≤ right i) :
    terminalArmSecond kv right < terminalArmSum ku left ∨
      terminalArmSecond ku left < terminalArmSum kv right ∨
      ((∀ i, left i = 1) ∧ ∀ i, right i = 1) ∨
      (ku = 0 ∧ kv = 0 ∧ left (armFirstIndex ku) = 1 ∧
        right (armFirstIndex kv) = 1 ∧
        terminalArmSecond ku left = terminalArmSecond kv right ∧
        2 ≤ terminalArmSecond ku left) := by
  by_cases hstrictLeft : terminalArmSecond kv right < terminalArmSum ku left
  · exact Or.inl hstrictLeft
  by_cases hstrictRight : terminalArmSecond ku left < terminalArmSum kv right
  · exact Or.inr (Or.inl hstrictRight)
  have hl := terminal_arm_second_le_sum ku left hleft hleftPos
  have hr := terminal_arm_second_le_sum kv right hright hrightPos
  have heqL : terminalArmSum ku left = terminalArmSecond ku left := by omega
  have heqR : terminalArmSum kv right = terminalArmSecond kv right := by omega
  have heq : terminalArmSecond ku left = terminalArmSecond kv right := by omega
  have hlpos := hleftPos (armSecondIndex ku)
  by_cases hone : terminalArmSecond ku left = 1
  · have hsumL : terminalArmSum ku left = 1 := heqL.trans hone
    have hsumR : terminalArmSum kv right = 1 := heqR.trans (heq.symm.trans hone)
    exact Or.inr (Or.inr (Or.inl
      ⟨(terminal_arm_sum_eq_one_iff ku left hleft hleftPos).mp hsumL,
        (terminal_arm_sum_eq_one_iff kv right hright hrightPos).mp hsumR⟩))
  · have hsecondL : 2 ≤ terminalArmSecond ku left := by
      change 1 ≤ terminalArmSecond ku left at hlpos
      omega
    have hsecondR : 2 ≤ terminalArmSecond kv right := by omega
    have hpairL := (terminal_arm_sum_eq_second_iff ku left hleft hleftPos hsecondL).mp heqL
    have hpairR := (terminal_arm_sum_eq_second_iff kv right hright hrightPos hsecondR).mp heqR
    exact Or.inr (Or.inr (Or.inr
      ⟨hpairL.1, hpairR.1, hpairL.2, hpairR.2, heq, hsecondL⟩))

end FaultObservationResearch
