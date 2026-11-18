module

public import «formalization-foundations»
public import Mathlib.Data.List.Nodup

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

abbrev Neighbors (n : ℕ) := Fin n → List (Fin n)

variable {n : ℕ}

def adj (nbr : Neighbors n) (a b : Fin n) : Prop := b ∈ nbr a

def colors (n : ℕ) (mask : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => mask.testBit v.val)

/-- Compute a bit using division and remainder, both evaluated efficiently
by Lean on natural number literals. -/
def fastBit (mask bit : ℕ) : Bool := (mask / 2 ^ bit % 2) == 1

theorem fastBit_eq (mask bit : ℕ) : fastBit mask bit = mask.testBit bit := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  exact Bool.eq_iff_iff.mpr (by simp [fastBit, beq_iff_eq, decide_eq_true_eq])

@[simp] theorem mem_colors (mask : ℕ) (v : Fin n) :
    v ∈ colors n mask ↔ mask.testBit v.val = true := by
  simp [colors]

def remove (mask loss : ℕ) : ℕ := mask &&& (mask ^^^ loss)

theorem colors_remove (mask loss : ℕ) :
    colors n (remove mask loss) = colors n mask \ colors n loss := by
  ext v
  simp only [mem_colors, Finset.mem_sdiff, remove, Nat.testBit_and, Nat.testBit_xor]
  cases hMask : mask.testBit v.val <;> cases hLoss : loss.testBit v.val <;> decide

theorem colors_single (v : Fin n) : colors n (2 ^ v.val) = {v} := by
  ext w
  simp only [mem_colors, Nat.testBit_two_pow, Finset.mem_singleton, decide_eq_true_eq]
  exact ⟨fun h => Fin.ext h.symm, fun h => congrArg Fin.val h.symm⟩

def forcedVertex (neighbors : List (Fin n)) (mask : ℕ) : Option (Fin n) :=
  match neighbors.filter (fun v => !(fastBit mask v.val)) with
  | [v] => some v
  | _ => none

private theorem filtered_singleton {α : Type} {l : List α} {v : α} (distinct : l.Nodup) :
    l = [v] ↔ v ∈ l ∧ ∀ w ∈ l, w = v := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hv, hUnique⟩
    cases l with
    | nil => simp at hv
    | cons a tail =>
      have ha := hUnique a (by simp : a ∈ a :: tail)
      cases tail with
      | nil => simp [ha]
      | cons b rest =>
        have hb := hUnique b (by simp : b ∈ a :: b :: rest)
        have heq : a = b := ha.trans hb.symm
        have hForbid := (List.nodup_cons.mp distinct).1
        exact False.elim (hForbid (by simp [heq]))

theorem forcedVertex_spec (neighbors : List (Fin n)) (distinct : neighbors.Nodup)
    (mask : ℕ) (v : Fin n) :
    forcedVertex neighbors mask = some v ↔
      v ∈ neighbors ∧ v ∉ colors n mask ∧
        ∀ w ∈ neighbors, w ∉ colors n mask → w = v := by
  let p : Fin n → Bool := fun w => !(mask.testBit w.val)
  have hFilter : ∀ w, w ∈ neighbors.filter p ↔ w ∈ neighbors ∧ w ∉ colors n mask := by
    intro w
    simp [p]
  have hSingleton : forcedVertex neighbors mask = some v ↔ neighbors.filter p = [v] := by
    simp only [forcedVertex, fastBit_eq]
    change (match neighbors.filter p with | [w] => some w | _ => none) = some v ↔ _
    rcases neighbors.filter p with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp
  rw [hSingleton, filtered_singleton (distinct.filter p)]
  simp only [hFilter]
  constructor
  · rintro ⟨⟨hv, hWhite⟩, hUnique⟩
    exact ⟨hv, hWhite, fun w hw h => hUnique w ⟨hw, h⟩⟩
  · rintro ⟨hv, hWhite, hUnique⟩
    exact ⟨⟨hv, hWhite⟩, fun w h => hUnique w h.1 h.2⟩

def contribution (nbr : Neighbors n) (mask : ℕ) (source : Fin n) : ℕ :=
  if fastBit mask source.val then
    match forcedVertex (nbr source) mask with
    | some v => 2 ^ v.val
    | none => 0
  else 0

def forces (nbr : Neighbors n) (mask : ℕ) : List (Fin n) → ℕ
  | [] => 0
  | s :: tail => contribution nbr mask s ||| forces nbr mask tail

def step (nbr : Neighbors n) (mask : ℕ) : ℕ :=
  mask ||| forces nbr mask (List.finRange n)

private theorem contribution_bit (nbr : Neighbors n) (mask : ℕ) (source v : Fin n) :
    (contribution nbr mask source).testBit v.val = true ↔
      source ∈ colors n mask ∧ forcedVertex (nbr source) mask = some v := by
  simp only [contribution, fastBit_eq]
  rw [mem_colors]
  cases mask.testBit source.val
  · simp
  · simp only [ite_true, true_and]
    cases hf : forcedVertex (nbr source) mask with
    | none => simp
    | some w =>
      simp only [Nat.testBit_two_pow, decide_eq_true_eq, Option.some.injEq]
      exact ⟨Fin.ext, congrArg Fin.val⟩

private theorem forces_bit (nbr : Neighbors n) (mask : ℕ) (v : Fin n)
    (sources : List (Fin n)) :
    (forces nbr mask sources).testBit v.val = true ↔
      ∃ s ∈ sources, s ∈ colors n mask ∧ forcedVertex (nbr s) mask = some v := by
  induction sources with
  | nil => simp [forces]
  | cons s tail ih =>
    simp only [forces, Nat.testBit_or, Bool.or_eq_true, contribution_bit, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact ⟨s, Or.inl rfl, h⟩
      · exact ⟨x, Or.inr hx, h⟩
    · rintro ⟨x, h | h, hx⟩
      · subst x
        exact Or.inl hx
      · exact Or.inr ⟨x, h, hx⟩

theorem step_agrees (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup) (mask : ℕ) :
    colors n (step nbr mask) = synchronousStep (adj nbr) (colors n mask) := by
  ext v
  simp only [mem_synchronousStep, mem_colors, step, Nat.testBit_or, Bool.or_eq_true, forces_bit,
    List.mem_finRange, true_and, forcedVertex_spec _ (distinct _), adj]
  constructor
  · rintro (h | ⟨s, hs, hv, _, hu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, hv, hu⟩
  · rintro (h | ⟨s, hs, hv, hu⟩)
    · exact Or.inl h
    · by_cases h : mask.testBit v.val = true
      · exact Or.inl h
      · exact Or.inr ⟨s, hs, hv, h, hu⟩

/-- Stop at a fixed point or when the requested round is reached. -/
def run (nbr : Neighbors n) (mask : ℕ) : ℕ → ℕ
  | 0 => mask
  | t + 1 =>
    let next := step nbr mask
    if next == mask then mask else run nbr next t

theorem run_agrees (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup) (mask t : ℕ) :
    colors n (run nbr mask t) = colorAfter (adj nbr) (colors n mask) t := by
  induction t generalizing mask with
  | zero => rfl
  | succ t ih =>
    have hAdd : colorAfter (adj nbr) (colors n mask) (t + 1) =
        colorAfter (adj nbr) (synchronousStep (adj nbr) (colors n mask)) t := by
      rw [show t + 1 = 1 + t by omega, colorAfter_add]
      rfl
    rw [hAdd, ← step_agrees nbr distinct mask]
    unfold run
    by_cases h : step nbr mask = mask
    · simp only [h, beq_self_eq_true, ite_true]
      refine (colorAfter_of_fixed (adj nbr) (colors n mask) ?_ t).symm
      rw [← step_agrees nbr distinct mask, h]
    · simp only [beq_eq_false_iff_ne.mpr h, Bool.false_eq_true, ite_false]
      exact ih (step nbr mask)

def fullMask (n mask : ℕ) : Bool := (mask % 2 ^ n) == (2 ^ n - 1)

theorem fullMask_agrees (n mask : ℕ) :
    fullMask n mask = true ↔ colors n mask = Finset.univ := by
  rw [fullMask, beq_iff_eq, Finset.eq_univ_iff_forall]
  constructor
  · intro h v
    have hb := congrArg (fun k : ℕ => k.testBit v.val) h
    simpa [Nat.testBit_mod_two_pow, v.isLt] using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro v
    by_cases hv : v < n
    · have hb := (mem_colors mask ⟨v, hv⟩).mp (h ⟨v, hv⟩)
      simp [Nat.testBit_mod_two_pow, hv, hb]
    · simp [Nat.testBit_mod_two_pow, hv]

def finishes (nbr : Neighbors n) (start round : ℕ) : Bool :=
  fullMask n (run nbr start round)

theorem finishes_agrees (nbr : Neighbors n) (distinct : ∀ v, (nbr v).Nodup)
    (mask t : ℕ) : finishes nbr mask t = true ↔ FinishesBy (adj nbr) (colors n mask) t := by
  unfold finishes FinishesBy
  rw [fullMask_agrees, run_agrees nbr distinct mask t]

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.finishes_agrees
