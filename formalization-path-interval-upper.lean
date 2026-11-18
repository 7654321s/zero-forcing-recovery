module

/-
Completion bounds for an interval inside the original path, with active blue guards.
White vertices outside the interval are retained in the model.
These tools do not assert the arbitrary-B every-minimum-support theorem.
-/
public import «formalization-path-gap»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

def PathIntervalWhites (n : ℕ) (blue : Finset (Fin (n + 1))) (left right : Fin (n + 1)) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun x => left.val ≤ x.val ∧ x.val ≤ right.val ∧ x ∉ blue)

def PathLeftReady (n : ℕ) (blue : Finset (Fin (n + 1))) (left : Fin (n + 1)) : Prop :=
  left ∈ blue ∧ ∀ x : Fin (n + 1), (SimpleGraph.pathGraph (n + 1)).Adj left x →
    x.val < left.val → x ∈ blue

def PathRightReady (n : ℕ) (blue : Finset (Fin (n + 1))) (right : Fin (n + 1)) : Prop :=
  right ∈ blue ∧ ∀ x : Fin (n + 1), (SimpleGraph.pathGraph (n + 1)).Adj right x →
    right.val < x.val → x ∈ blue

theorem pathIntervalWhites_antitone (n : ℕ) (A B : Finset (Fin (n + 1)))
    (hsub : A ⊆ B) (left right : Fin (n + 1)) :
    PathIntervalWhites n B left right ⊆ PathIntervalWhites n A left right := by
  classical
  intro x hx
  have hi := (Finset.mem_filter.mp hx).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.1, hi.2.1, fun h => hi.2.2 (hsub h)⟩

theorem pathLeftReady_mono (n : ℕ) (A B : Finset (Fin (n + 1)))
    (hsub : A ⊆ B) (left : Fin (n + 1)) (hready : PathLeftReady n A left) :
    PathLeftReady n B left :=
  ⟨hsub hready.1, fun x ha hl => hsub (hready.2 x ha hl)⟩

theorem pathRightReady_mono (n : ℕ) (A B : Finset (Fin (n + 1)))
    (hsub : A ⊆ B) (right : Fin (n + 1)) (hready : PathRightReady n A right) :
    PathRightReady n B right :=
  ⟨hsub hready.1, fun x ha hr => hsub (hready.2 x ha hr)⟩

theorem path_interval_min_mem_step (n : ℕ) (blue : Finset (Fin (n + 1)))
    (left right : Fin (n + 1)) (hready : PathLeftReady n blue left)
    (hne : (PathIntervalWhites n blue left right).Nonempty) :
    (PathIntervalWhites n blue left right).min' hne ∈
      synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj blue := by
  classical
  let W := PathIntervalWhites n blue left right
  let m := W.min' hne
  have hmW : m ∈ W := W.min'_mem hne
  have hm := (Finset.mem_filter.mp hmW).2
  have hmLow : left.val ≤ m.val := hm.1
  have hmHigh : m.val ≤ right.val := hm.2.1
  have hlm : left.val < m.val := by
    have hneval : m.val ≠ left.val := by
      intro h
      have heq : m = left := Fin.ext h
      exact hm.2.2 (by rw [heq]; exact hready.1)
    omega
  let source : Fin (n + 1) := ⟨m.val - 1, by have := m.isLt; omega⟩
  have hsourceVal : source.val = m.val - 1 := rfl
  have hsLeft : left.val ≤ source.val := by dsimp [source]; omega
  have hsRight : source.val ≤ right.val := by dsimp [source]; omega
  have hs : source ∈ blue := by
    by_cases heq : source = left
    · rw [heq]
      exact hready.1
    · by_contra hnot
      have hsW : source ∈ W :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsLeft, hsRight, hnot⟩
      have hle : m.val ≤ source.val := W.min'_le source hsW
      change m.val ≤ m.val - 1 at hle
      omega
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨source, hs, ?_, ?_⟩
  · apply SimpleGraph.pathGraph_adj.mpr
    left
    change m.val - 1 + 1 = m.val
    omega
  · intro other hadj hw
    rcases SimpleGraph.pathGraph_adj.mp hadj with hright | hleft
    · have hv : other.val = m.val := by
        change m.val - 1 + 1 = other.val at hright
        omega
      exact Fin.ext hv
    · have hoLess : other.val < m.val := by
        change other.val + 1 = m.val - 1 at hleft
        omega
      by_cases hbefore : other.val < left.val
      · have hsEq : source = left := by
          apply Fin.ext
          change other.val + 1 = source.val at hleft
          omega
        have ha : (SimpleGraph.pathGraph (n + 1)).Adj left other := by
          rw [← hsEq]
          exact hadj
        exact False.elim (hw (hready.2 other ha hbefore))
      · have hoW : other ∈ W := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by omega, by omega, hw⟩
        have hle : m.val ≤ other.val := W.min'_le other hoW
        omega

theorem path_interval_max_mem_step (n : ℕ) (blue : Finset (Fin (n + 1)))
    (left right : Fin (n + 1)) (hready : PathRightReady n blue right)
    (hne : (PathIntervalWhites n blue left right).Nonempty) :
    (PathIntervalWhites n blue left right).max' hne ∈
      synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj blue := by
  classical
  let W := PathIntervalWhites n blue left right
  let m := W.max' hne
  have hmW : m ∈ W := W.max'_mem hne
  have hm := (Finset.mem_filter.mp hmW).2
  have hmLow : left.val ≤ m.val := hm.1
  have hmHigh : m.val ≤ right.val := hm.2.1
  have hmr : m.val < right.val := by
    have hneval : m.val ≠ right.val := by
      intro h
      have heq : m = right := Fin.ext h
      exact hm.2.2 (by rw [heq]; exact hready.1)
    omega
  let source : Fin (n + 1) := ⟨m.val + 1, by have := right.isLt; omega⟩
  have hsourceVal : source.val = m.val + 1 := rfl
  have hsLeft : left.val ≤ source.val := by dsimp [source]; omega
  have hsRight : source.val ≤ right.val := by dsimp [source]; omega
  have hs : source ∈ blue := by
    by_cases heq : source = right
    · rw [heq]
      exact hready.1
    · by_contra hnot
      have hsW : source ∈ W :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsLeft, hsRight, hnot⟩
      have hle : source.val ≤ m.val := W.le_max' source hsW
      change m.val + 1 ≤ m.val at hle
      omega
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨source, hs, SimpleGraph.pathGraph_adj.mpr (Or.inr rfl), ?_⟩
  intro other hadj hw
  rcases SimpleGraph.pathGraph_adj.mp hadj with hright | hleft
  · have hoMore : m.val < other.val := by
      change m.val + 1 + 1 = other.val at hright
      omega
    by_cases hafter : right.val < other.val
    · have hsEq : source = right := by
        apply Fin.ext
        change source.val + 1 = other.val at hright
        omega
      have ha : (SimpleGraph.pathGraph (n + 1)).Adj right other := by
        rw [← hsEq]
        exact hadj
      exact False.elim (hw (hready.2 other ha hafter))
    · have hoW : other ∈ W := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by omega, by omega, hw⟩
      have hle : other.val ≤ m.val := W.le_max' other hoW
      omega
  · have hv : other.val = m.val := by
      change other.val + 1 = m.val + 1 at hleft
      omega
    exact Fin.ext hv

theorem path_interval_next_whites_subset_erase_max (n : ℕ) (blue : Finset (Fin (n + 1)))
    (left right : Fin (n + 1)) (hready : PathRightReady n blue right)
    (hne : (PathIntervalWhites n blue left right).Nonempty) :
    PathIntervalWhites n (synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj blue) left right ⊆
      (PathIntervalWhites n blue left right).erase ((PathIntervalWhites n blue left right).max' hne) := by
  classical
  have hmax := path_interval_max_mem_step n blue left right hready hne
  intro x hx
  have hi := (Finset.mem_filter.mp hx).2
  have hOld := pathIntervalWhites_antitone n blue _ (subset_synchronousStep _ _) left right hx
  apply Finset.mem_erase.mpr
  refine ⟨?_, hOld⟩
  intro heq
  exact hi.2.2 (by rw [heq]; exact hmax)

theorem path_interval_next_whites_subset_erase_extremes (n : ℕ) (blue : Finset (Fin (n + 1)))
    (left right : Fin (n + 1)) (hleft : PathLeftReady n blue left)
    (hright : PathRightReady n blue right)
    (hne : (PathIntervalWhites n blue left right).Nonempty) :
    PathIntervalWhites n (synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj blue) left right ⊆
      erasePathExtremes n (PathIntervalWhites n blue left right) hne := by
  classical
  have hmin := path_interval_min_mem_step n blue left right hleft hne
  intro x hx
  have hi := (Finset.mem_filter.mp hx).2
  have hrightE := path_interval_next_whites_subset_erase_max n blue left right hright hne hx
  refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hrightE).1, ?_⟩
  refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_erase.mp hrightE).2⟩
  intro heq
  exact hi.2.2 (by rw [heq]; exact hmin)

theorem path_interval_one_sided_upper (n : ℕ) (blue : Finset (Fin (n + 1)))
    (left right : Fin (n + 1)) (hright : PathRightReady n blue right) (deadline : ℕ)
    (hcount : (PathIntervalWhites n blue left right).card ≤ deadline) :
    ∀ x : Fin (n + 1), left.val ≤ x.val → x.val ≤ right.val →
      x ∈ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj blue deadline := by
  classical
  have general : ∀ m : ℕ, ∀ B : Finset (Fin (n + 1)),
      (PathIntervalWhites n B left right).card = m → PathRightReady n B right →
      ∀ t : ℕ, (PathIntervalWhites n B left right).card ≤ t →
        ∀ x : Fin (n + 1), left.val ≤ x.val → x.val ≤ right.val →
          x ∈ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj B t := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro B hcard hR t hc
      let W := PathIntervalWhites n B left right
      have hWcard : W.card = m := hcard
      have hWcount : W.card ≤ t := hc
      by_cases hempty : W = ∅
      · intro x hxl hxr
        have hxB : x ∈ B := by
          by_contra hnot
          have hxW : x ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxl, hxr, hnot⟩
          rw [hempty] at hxW
          simp at hxW
        exact colorAfter_mono_time (SimpleGraph.pathGraph (n + 1)).Adj B (Nat.zero_le t) hxB
      · have hne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        have hpos : 0 < W.card := Finset.card_pos.mpr hne
        cases t with
        | zero => omega
        | succ t =>
          let C := synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj B
          let S := PathIntervalWhites n C left right
          have hsCard : S.card ≤ W.card - 1 := by
            have hsub := path_interval_next_whites_subset_erase_max n B left right hR hne
            have hle := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem (W.max'_mem hne)] at hle
            exact hle
          have hCR : PathRightReady n C right :=
            pathRightReady_mono n B C (subset_synchronousStep _ _) right hR
          have hsStrict : S.card < m := by omega
          have hsTime : (PathIntervalWhites n C left right).card ≤ t := by
            change S.card ≤ t
            omega
          have hf := ih S.card hsStrict C rfl hCR t hsTime
          have hshift := colorAfter_add (SimpleGraph.pathGraph (n + 1)).Adj B 1 t
          change colorAfter _ _ (1 + t) = colorAfter _ C t at hshift
          rw [Nat.add_comm 1 t] at hshift
          intro x hxl hxr
          rw [hshift]
          exact hf x hxl hxr
  exact general _ blue rfl hright deadline hcount

theorem path_interval_two_sided_upper (n : ℕ) (blue : Finset (Fin (n + 1)))
    (left right : Fin (n + 1)) (hleft : PathLeftReady n blue left)
    (hright : PathRightReady n blue right) (deadline : ℕ)
    (hcount : (PathIntervalWhites n blue left right).card ≤ 2 * deadline) :
    ∀ x : Fin (n + 1), left.val ≤ x.val → x.val ≤ right.val →
      x ∈ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj blue deadline := by
  classical
  have general : ∀ m : ℕ, ∀ B : Finset (Fin (n + 1)),
      (PathIntervalWhites n B left right).card = m → PathLeftReady n B left →
      PathRightReady n B right → ∀ t : ℕ, (PathIntervalWhites n B left right).card ≤ 2 * t →
        ∀ x : Fin (n + 1), left.val ≤ x.val → x.val ≤ right.val →
          x ∈ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj B t := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro B hcard hL hR t hc
      let W := PathIntervalWhites n B left right
      have hWcard : W.card = m := hcard
      have hWcount : W.card ≤ 2 * t := hc
      by_cases hempty : W = ∅
      · intro x hxl hxr
        have hxB : x ∈ B := by
          by_contra hnot
          have hxW : x ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxl, hxr, hnot⟩
          rw [hempty] at hxW
          simp at hxW
        exact colorAfter_mono_time (SimpleGraph.pathGraph (n + 1)).Adj B (Nat.zero_le t) hxB
      · have hne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        have hpos : 0 < W.card := Finset.card_pos.mpr hne
        cases t with
        | zero => omega
        | succ t =>
          let C := synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj B
          let S := PathIntervalWhites n C left right
          have hsCard : S.card ≤ W.card - 2 := by
            have hsub := path_interval_next_whites_subset_erase_extremes n B left right hL hR hne
            have hle := Finset.card_le_card hsub
            rw [erasePathExtremes_card n W hne] at hle
            exact hle
          have hCL : PathLeftReady n C left :=
            pathLeftReady_mono n B C (subset_synchronousStep _ _) left hL
          have hCR : PathRightReady n C right :=
            pathRightReady_mono n B C (subset_synchronousStep _ _) right hR
          have hsStrict : S.card < m := by omega
          have hsTime : (PathIntervalWhites n C left right).card ≤ 2 * t := by
            change S.card ≤ 2 * t
            omega
          have hf := ih S.card hsStrict C rfl hCL hCR t hsTime
          have hshift := colorAfter_add (SimpleGraph.pathGraph (n + 1)).Adj B 1 t
          change colorAfter _ _ (1 + t) = colorAfter _ C t at hshift
          rw [Nat.add_comm 1 t] at hshift
          intro x hxl hxr
          rw [hshift]
          exact hf x hxl hxr
  exact general _ blue rfl hleft hright deadline hcount

end FaultObservationResearch
