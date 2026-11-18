module

/-
Arithmetic split used after extracting two terminal pendant structures.
The strict-comparison/equality method is prior; graph extraction is not proved here.
-/
public import «formalization-foundations»

@[expose] public section

set_option autoImplicit false
namespace FaultObservationResearch

def armFirstIndex (k : ℕ) : Fin (k + 2) := ⟨0, by omega⟩
def armSecondIndex (k : ℕ) : Fin (k + 2) := ⟨1, by omega⟩
def armPenultimateIndex (k : ℕ) : Fin (k + 2) := ⟨k, by omega⟩
def terminalArmSecond (k : ℕ) (lengths : Fin (k + 2) → ℕ) : ℕ :=
  lengths (armSecondIndex k)
def terminalArmSum (k : ℕ) (lengths : Fin (k + 2) → ℕ) : ℕ :=
  lengths (Fin.last (k + 1)) + lengths (armPenultimateIndex k) - 1

theorem terminal_arm_second_le_sum (k : ℕ) (lengths : Fin (k + 2) → ℕ)
    (hmono : Monotone lengths) (hpos : ∀ i, 1 ≤ lengths i) :
    terminalArmSecond k lengths ≤ terminalArmSum k lengths := by
  have hlast : lengths (armSecondIndex k) ≤ lengths (Fin.last (k + 1)) :=
    hmono (by change 1 ≤ k + 1; omega)
  have hprev := hpos (armPenultimateIndex k)
  dsimp [terminalArmSecond, terminalArmSum]
  omega

theorem terminal_arm_sum_eq_second_iff (k : ℕ) (lengths : Fin (k + 2) → ℕ)
    (hmono : Monotone lengths) (hpos : ∀ i, 1 ≤ lengths i)
    (hsecond : 2 ≤ terminalArmSecond k lengths) :
    terminalArmSum k lengths = terminalArmSecond k lengths ↔
      k = 0 ∧ lengths (armFirstIndex k) = 1 := by
  constructor
  · intro heq
    have hlast : lengths (armSecondIndex k) ≤ lengths (Fin.last (k + 1)) :=
      hmono (by change 1 ≤ k + 1; omega)
    have hprev := hpos (armPenultimateIndex k)
    have hone : lengths (armPenultimateIndex k) ≤ 1 := by
      dsimp [terminalArmSum, terminalArmSecond] at heq
      omega
    have hk : k = 0 := by
      by_contra hne
      have hsp : lengths (armSecondIndex k) ≤ lengths (armPenultimateIndex k) :=
        hmono (by change 1 ≤ k; omega)
      dsimp [terminalArmSecond] at hsecond
      omega
    subst k
    refine ⟨rfl, ?_⟩
    exact Nat.le_antisymm hone (hpos _)
  · rintro ⟨hk, hfirst⟩
    subst k
    change lengths (armSecondIndex 0) + lengths (armFirstIndex 0) - 1 =
      lengths (armSecondIndex 0)
    rw [hfirst]
    omega

theorem terminal_arm_strict_or_matching
    (ku kv : ℕ) (left : Fin (ku + 2) → ℕ) (right : Fin (kv + 2) → ℕ)
    (hleft : Monotone left) (hright : Monotone right)
    (hleftPos : ∀ i, 1 ≤ left i) (hrightPos : ∀ i, 1 ≤ right i)
    (hleftSecond : 2 ≤ terminalArmSecond ku left)
    (hrightSecond : 2 ≤ terminalArmSecond kv right) :
    terminalArmSecond kv right < terminalArmSum ku left ∨
      terminalArmSecond ku left < terminalArmSum kv right ∨
      (ku = 0 ∧ kv = 0 ∧ left (armFirstIndex ku) = 1 ∧
        right (armFirstIndex kv) = 1 ∧
        terminalArmSecond ku left = terminalArmSecond kv right) := by
  by_cases hstrictLeft : terminalArmSecond kv right < terminalArmSum ku left
  · exact Or.inl hstrictLeft
  by_cases hstrictRight : terminalArmSecond ku left < terminalArmSum kv right
  · exact Or.inr (Or.inl hstrictRight)
  have hl := terminal_arm_second_le_sum ku left hleft hleftPos
  have hr := terminal_arm_second_le_sum kv right hright hrightPos
  have heqL : terminalArmSum ku left = terminalArmSecond ku left := by omega
  have heqR : terminalArmSum kv right = terminalArmSecond kv right := by omega
  have hpairL := (terminal_arm_sum_eq_second_iff ku left hleft hleftPos hleftSecond).mp heqL
  have hpairR := (terminal_arm_sum_eq_second_iff kv right hright hrightPos hrightSecond).mp heqR
  exact Or.inr (Or.inr ⟨hpairL.1, hpairR.1, hpairL.2, hpairR.2, by omega⟩)

end FaultObservationResearch
