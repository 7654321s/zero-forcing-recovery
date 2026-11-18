module

public import MaskForcing

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

variable {n : ℕ}

/-- Adding a power of two to a mask whose corresponding bit is zero
sets just that bit. -/
theorem add_bit_eq_or (mask bit : ℕ) (unset : mask.testBit bit = false) :
    mask + 2 ^ bit = mask ||| 2 ^ bit := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  rcases lt_trichotomy i bit with hLower | rfl | hHigher
  · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hLower]
    simp [show bit ≠ i by omega]
  · rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, unset]
    simp
  · have hEven : mask / 2 ^ bit % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at unset
      have hNe : mask / 2 ^ bit % 2 ≠ 1 := by
        intro h
        rw [h] at unset
        contradiction
      omega
    let q := mask / 2 ^ bit / 2
    let r := mask % 2 ^ bit
    have hQR : mask / 2 ^ bit = 2 * q := by
      have h := Nat.div_add_mod (mask / 2 ^ bit) 2
      rw [hEven, Nat.add_zero] at h
      exact h.symm
    have hRest : r < 2 ^ bit := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hRebuild : mask = 2 ^ (bit + 1) * q + r := by
      calc
        mask = 2 ^ bit * (mask / 2 ^ bit) + r := (Nat.div_add_mod _ _).symm
        _ = 2 ^ (bit + 1) * q + r := by simp [hQR, Nat.pow_succ, Nat.mul_assoc]
    have hSmall : r + 2 ^ bit < 2 ^ (bit + 1) := by
      rw [Nat.pow_succ]
      omega
    have hOld : mask / 2 ^ (bit + 1) = q := by
      rw [hRebuild, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (by omega :
        r < 2 ^ (bit + 1)), Nat.add_zero]
    have hPlus : (mask + 2 ^ bit) / 2 ^ (bit + 1) = q := by
      rw [hRebuild, Nat.add_assoc, Nat.mul_add_div (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hSmall, Nat.add_zero]
    simp only [show bit ≠ i by omega, decide_false, Bool.or_false]
    rw [show i = (i - (bit + 1)) + (bit + 1) by omega]
    simp only [Nat.testBit_add, hOld, hPlus]

def insertBit (mask bit : ℕ) : ℕ :=
  if fastBit mask bit then mask else mask + 2 ^ bit

theorem insertBit_eq_or (mask bit : ℕ) : insertBit mask bit = mask ||| 2 ^ bit := by
  unfold insertBit
  rw [fastBit_eq]
  cases h : mask.testBit bit
  · exact add_bit_eq_or mask bit h
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.testBit_two_pow]
    by_cases hEq : bit = i
    · subst i
      simp [h]
    · simp [hEq]

def accumulate (nbr : Neighbors n) (mask : ℕ) (source : Fin n) (acc : ℕ) : ℕ :=
  if fastBit mask source.val then
    match forcedVertex (nbr source) mask with
    | none => acc
    | some v => insertBit acc v.val
  else acc

theorem accumulate_eq (nbr : Neighbors n) (mask : ℕ) (source : Fin n) (acc : ℕ) :
    accumulate nbr mask source acc = acc ||| contribution nbr mask source := by
  unfold accumulate contribution
  cases fastBit mask source.val
  · simp
  · cases forcedVertex (nbr source) mask <;> simp [insertBit_eq_or]

def scan (nbr : Neighbors n) (mask : ℕ) : List (Fin n) → ℕ → ℕ
  | [], acc => acc
  | source :: tail, acc => scan nbr mask tail (accumulate nbr mask source acc)

theorem scan_eq (nbr : Neighbors n) (mask : ℕ) (sources : List (Fin n)) (acc : ℕ) :
    scan nbr mask sources acc = acc ||| forces nbr mask sources := by
  induction sources generalizing acc with
  | nil => simp [scan, forces]
  | cons s tail ih => simp only [scan, forces, ih, accumulate_eq, Nat.or_assoc]

def fastStep (nbr : Neighbors n) (mask : ℕ) : ℕ :=
  scan nbr mask (List.finRange n) mask

theorem fastStep_eq (nbr : Neighbors n) (mask : ℕ) : fastStep nbr mask = step nbr mask :=
  scan_eq nbr mask (List.finRange n) mask

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.fastStep_eq
