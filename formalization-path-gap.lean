module

/-
Synchronous dynamics of a white gap with no active blue pair inside it.
These lemmas are tools for the arbitrary-B path proof, not that theorem itself.
-/
public import «formalization-path-full-blue»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

/-- Every adjacent blue pair lies entirely to one side of the remaining white gap. -/
def PathWhiteGap (n : ℕ) (white : Finset (Fin (n + 1))) : Prop :=
  ∀ x y : Fin (n + 1), x ∉ white → y ∉ white → x.val + 1 = y.val →
    ∀ a ∈ white, ∀ b ∈ white, a.val < x.val → y.val < b.val → False

def erasePathExtremes (n : ℕ) (white : Finset (Fin (n + 1))) (hne : white.Nonempty) :
    Finset (Fin (n + 1)) := (white.erase (white.min' hne)).erase (white.max' hne)

theorem path_min_white_mem_step (n : ℕ) (white : Finset (Fin (n + 1)))
    (hne : white.Nonempty) (hzero : (0 : Fin (n + 1)) ∉ white) :
    white.min' hne ∈ synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ white) := by
  classical
  let m := white.min' hne
  have hm : m ∈ white := white.min'_mem hne
  have hm0 : 0 < m.val := by
    by_contra h
    have hmval : m.val = 0 := by omega
    have heq : m = 0 := Fin.ext hmval
    exact hzero (by rwa [← heq])
  let source : Fin (n + 1) := ⟨m.val - 1, by have := m.isLt; omega⟩
  have hsNot : source ∉ white := by
    intro hs
    have hle : m.val ≤ source.val := white.min'_le source hs
    change m.val ≤ m.val - 1 at hle
    omega
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨source, by simp [hsNot], ?_, ?_⟩
  · apply SimpleGraph.pathGraph_adj.mpr
    left
    change m.val - 1 + 1 = m.val
    omega
  · intro other ha hw
    have ho : other ∈ white := by simpa using hw
    have hle : m.val ≤ other.val := white.min'_le other ho
    rcases SimpleGraph.pathGraph_adj.mp ha with hright | hleft
    · apply Fin.ext
      change m.val - 1 + 1 = other.val at hright
      omega
    · change other.val + 1 = m.val - 1 at hleft
      omega

theorem path_gap_blue_neighbor_white (n : ℕ) (white : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (source a b : Fin (n + 1))
    (hs : source ∉ white) (ha : a ∈ white) (hb : b ∈ white)
    (has : a.val < source.val) (hsb : source.val < b.val)
    (other : Fin (n + 1)) (hadj : (SimpleGraph.pathGraph (n + 1)).Adj source other) :
    other ∈ white := by
  by_contra ho
  rcases SimpleGraph.pathGraph_adj.mp hadj with hright | hleft
  · have hne : other.val ≠ b.val := by
      intro heq
      have heqFin : other = b := Fin.ext heq
      exact ho (by rwa [heqFin])
    exact hgap source other hs ho hright a ha b hb has (by omega)
  · have hne : other.val ≠ a.val := by
      intro heq
      have heqFin : other = a := Fin.ext heq
      exact ho (by rwa [heqFin])
    exact hgap other source ho hs hleft a ha b hb (by omega) hsb

theorem path_gap_step_subset (n : ℕ) (white : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hne : white.Nonempty) :
    synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ white) ⊆
      (Finset.univ \ white) ∪ {white.min' hne, white.max' hne} := by
  classical
  let a := white.min' hne
  let b := white.max' hne
  have ha : a ∈ white := white.min'_mem hne
  have hb : b ∈ white := white.max'_mem hne
  intro target ht
  by_cases hold : target ∈ Finset.univ \ white
  · exact Finset.mem_union.mpr (Or.inl hold)
  have htW : target ∈ white := by simpa using hold
  by_cases hext : target = a ∨ target = b
  · exact Finset.mem_union.mpr (Or.inr (by simpa only [Finset.mem_insert,
      Finset.mem_singleton] using hext))
  have haLe : a.val ≤ target.val := white.min'_le target htW
  have hbLe : target.val ≤ b.val := white.le_max' target htW
  have hta : a.val < target.val := by
    have hne : target.val ≠ a.val := fun h => hext (Or.inl (Fin.ext h))
    omega
  have htb : target.val < b.val := by
    have hne : target.val ≠ b.val := fun h => hext (Or.inr (Fin.ext h))
    omega
  rcases (mem_synchronousStep _ _ _).mp ht with h | ⟨source, hs, hadj, hu⟩
  · exact False.elim (hold h)
  · have hsNot : source ∉ white := (Finset.mem_sdiff.mp hs).2
    have hsNeA : source.val ≠ a.val := by
      intro h
      have heq : source = a := Fin.ext h
      exact hsNot (by rwa [heq])
    have hsNeB : source.val ≠ b.val := by
      intro h
      have heq : source = b := Fin.ext h
      exact hsNot (by rwa [heq])
    have has : a.val < source.val := by
      rcases SimpleGraph.pathGraph_adj.mp hadj with h | h <;> omega
    have hsb : source.val < b.val := by
      rcases SimpleGraph.pathGraph_adj.mp hadj with h | h <;> omega
    have hs0 : 0 < source.val := by omega
    have hsn : source.val < n := by have := b.isLt; omega
    let left : Fin (n + 1) := ⟨source.val - 1, by have := source.isLt; omega⟩
    let right : Fin (n + 1) := ⟨source.val + 1, by omega⟩
    have hleftEq : left.val + 1 = source.val := by dsimp [left]; omega
    have hleftAdj := SimpleGraph.pathGraph_adj.mpr (Or.inr hleftEq)
    have hrightAdj := SimpleGraph.pathGraph_adj.mpr (Or.inl (show source.val + 1 = right.val from rfl))
    have hleftW := path_gap_blue_neighbor_white n white hgap source a b hsNot ha hb has hsb left hleftAdj
    have hrightW := path_gap_blue_neighbor_white n white hgap source a b hsNot ha hb has hsb right hrightAdj
    have hl := hu left hleftAdj (by simp [hleftW])
    have hr := hu right hrightAdj (by simp [hrightW])
    have hv := congrArg Fin.val (hl.trans hr.symm)
    change source.val - 1 = source.val + 1 at hv
    omega

theorem path_gap_step (n : ℕ) (white : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hne : white.Nonempty)
    (hzero : (0 : Fin (n + 1)) ∉ white) (hlast : Fin.last n ∉ white) :
    synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ white) =
      Finset.univ \ erasePathExtremes n white hne := by
  classical
  have hmin := path_min_white_mem_step n white hne hzero
  have hmax := path_max_loss_mem_step n white hne hlast
  have hstep : synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ white) =
      (Finset.univ \ white) ∪ {white.min' hne, white.max' hne} := by
    apply le_antisymm (path_gap_step_subset n white hgap hne)
    intro x hx
    rcases Finset.mem_union.mp hx with hold | hext
    · exact subset_synchronousStep _ _ hold
    · rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hext) with h | h
      · simpa only [h] using hmin
      · simpa only [h] using hmax
  rw [hstep]
  ext x
  by_cases hminEq : x = white.min' hne <;>
    by_cases hmaxEq : x = white.max' hne <;> simp [erasePathExtremes, hminEq, hmaxEq]

theorem erasePathExtremes_subset (n : ℕ) (white : Finset (Fin (n + 1))) (hne : white.Nonempty) :
    erasePathExtremes n white hne ⊆ white := by
  intro x hx
  exact (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2

theorem pathWhiteGap_erase_extremes (n : ℕ) (white : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hne : white.Nonempty) :
    PathWhiteGap n (erasePathExtremes n white hne) := by
  classical
  intro x y hx hy hxy a ha b hb hax hyb
  have haW := erasePathExtremes_subset n white hne ha
  have hbW := erasePathExtremes_subset n white hne hb
  have middle : ∀ z : Fin (n + 1), a.val < z.val → z.val < b.val →
      z ∈ white → z ∈ erasePathExtremes n white hne := by
    intro z haz hzb hz
    have hmin : z ≠ white.min' hne := by
      intro heq
      have hle : (white.min' hne).val ≤ a.val := white.min'_le a haW
      have hv := congrArg Fin.val heq
      omega
    have hmax : z ≠ white.max' hne := by
      intro heq
      have hle : b.val ≤ (white.max' hne).val := white.le_max' b hbW
      have hv := congrArg Fin.val heq
      omega
    exact Finset.mem_erase.mpr ⟨hmax, Finset.mem_erase.mpr ⟨hmin, hz⟩⟩
  have hxW : x ∉ white := fun h => hx (middle x hax (by omega) h)
  have hyW : y ∉ white := fun h => hy (middle y (by omega) hyb h)
  exact hgap x y hxW hyW hxy a haW b hbW hax hyb

theorem erasePathExtremes_card (n : ℕ) (white : Finset (Fin (n + 1))) (hne : white.Nonempty) :
    (erasePathExtremes n white hne).card = white.card - 2 := by
  classical
  have hmin := white.min'_mem hne
  have hmax := white.max'_mem hne
  by_cases heq : white.min' hne = white.max' hne
  · have hall : ∀ x ∈ white, x = white.min' hne := by
      intro x hx
      apply Fin.ext
      have hl : (white.min' hne).val ≤ x.val := white.min'_le x hx
      have hr : x.val ≤ (white.max' hne).val := white.le_max' x hx
      have hv := congrArg Fin.val heq
      omega
    have hcard : white.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx y hy
      exact (hall x hx).trans (hall y hy).symm)
    have hempty : erasePathExtremes n white hne = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxW := erasePathExtremes_subset n white hne hx
      have hxNe := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      exact hxNe (hall x hxW)
    rw [hempty, Finset.card_empty]
    omega
  · have hmaxR : white.max' hne ∈ white.erase (white.min' hne) :=
      Finset.mem_erase.mpr ⟨Ne.symm heq, hmax⟩
    unfold erasePathExtremes
    rw [Finset.card_erase_of_mem hmaxR, Finset.card_erase_of_mem hmin]
    omega

theorem path_gap_finishes_iff (n : ℕ) (white : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hzero : (0 : Fin (n + 1)) ∉ white)
    (hlast : Fin.last n ∉ white) (deadline : ℕ) :
    FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ white) deadline ↔
      white.card ≤ 2 * deadline := by
  classical
  have general : ∀ m : ℕ, ∀ W : Finset (Fin (n + 1)), W.card = m →
      PathWhiteGap n W → (0 : Fin (n + 1)) ∉ W → Fin.last n ∉ W → ∀ t : ℕ,
      FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ W) t ↔ W.card ≤ 2 * t := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro W hcard hg hz hl t
      by_cases hempty : W = ∅
      · subst W
        simp [FinishesBy]
      · have hne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        have hpos : 0 < W.card := Finset.card_pos.mpr hne
        cases t with
        | zero =>
          constructor
          · intro hf
            have hx : W.min' hne ∈ Finset.univ \ W := by
              change Finset.univ \ W = Finset.univ at hf
              rw [hf]
              exact Finset.mem_univ _
            exact False.elim ((Finset.mem_sdiff.mp hx).2 (W.min'_mem hne))
          · intro h
            omega
        | succ t =>
          let S := erasePathExtremes n W hne
          have hsCard : S.card = W.card - 2 := erasePathExtremes_card n W hne
          have hsub : S ⊆ W := erasePathExtremes_subset n W hne
          have hSgap : PathWhiteGap n S := pathWhiteGap_erase_extremes n W hg hne
          have hSz : (0 : Fin (n + 1)) ∉ S := fun h => hz (hsub h)
          have hSl : Fin.last n ∉ S := fun h => hl (hsub h)
          have hshift := colorAfter_add (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ W) 1 t
          change colorAfter _ _ (1 + t) = colorAfter _ (synchronousStep _ (Finset.univ \ W)) t at hshift
          rw [Nat.add_comm 1 t, path_gap_step n W hg hne hz hl] at hshift
          change colorAfter _ _ (t + 1) = Finset.univ ↔ W.card ≤ 2 * (t + 1)
          rw [hshift]
          change FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ S) t ↔ W.card ≤ 2 * (t + 1)
          rw [ih S.card (by omega) S rfl hSgap hSz hSl t]
          omega
  exact general white.card white rfl hgap hzero hlast deadline

theorem path_gap_deadline_lower_bound (n : ℕ) (white blue : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hzero : (0 : Fin (n + 1)) ∉ white)
    (hlast : Fin.last n ∉ white) (hwhite : ∀ x ∈ white, x ∉ blue)
    (deadline : ℕ) (hfinish : FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj blue deadline) :
    white.card ≤ 2 * deadline := by
  classical
  have hsub : blue ⊆ Finset.univ \ white := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hw => hwhite x hw hx⟩
  exact (path_gap_finishes_iff n white hgap hzero hlast deadline).mp
    (FinishesBy_mono_blue _ hsub hfinish)

def PathWhiteInterval (n : ℕ) (blue support : Finset (Fin (n + 1))) (low high : ℕ) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun x => low ≤ x.val ∧ x.val ≤ high ∧ (x ∉ blue ∨ x ∈ support))

theorem pathWhiteGap_of_seed_hit_interval (n : ℕ) (blue support : Finset (Fin (n + 1)))
    (hcover : HitsPathSeeds n blue support) (low high : ℕ) :
    PathWhiteGap n (PathWhiteInterval n blue support low high) := by
  classical
  intro x y hx hy hxy a ha b hb hax hyb
  have haI := (Finset.mem_filter.mp ha).2
  have hbI := (Finset.mem_filter.mp hb).2
  have middle : ∀ z : Fin (n + 1), a.val ≤ z.val → z.val ≤ b.val →
      z ∉ PathWhiteInterval n blue support low high → z ∈ blue ∧ z ∉ support := by
    intro z haz hzb hz
    have hlow : low ≤ z.val := by omega
    have hhigh : z.val ≤ high := by omega
    constructor
    · by_contra hnot
      exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlow, hhigh, Or.inl hnot⟩)
    · intro h
      exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlow, hhigh, Or.inr h⟩)
  have hxB := middle x (by omega) (by omega) hx
  have hyB := middle y (by omega) (by omega) hy
  have hh := hcover.2.2 x y hxB.1 hyB.1 hxy
  exact hh.elim hxB.2 hyB.2

theorem path_interval_deadline_lower_bound (n : ℕ) (blue support : Finset (Fin (n + 1)))
    (hcover : HitsPathSeeds n blue support) (low high : ℕ) (hlow : 0 < low)
    (hhigh : high < n) (deadline : ℕ)
    (hfinish : FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj
      (blue \ support.filter (fun x => low ≤ x.val ∧ x.val ≤ high)) deadline) :
    (PathWhiteInterval n blue support low high).card ≤ 2 * deadline := by
  classical
  have hz : (0 : Fin (n + 1)) ∉ PathWhiteInterval n blue support low high := by
    intro h
    have hlo := (Finset.mem_filter.mp h).2.1
    change low ≤ 0 at hlo
    omega
  have hl : Fin.last n ∉ PathWhiteInterval n blue support low high := by
    intro h
    have hhi := (Finset.mem_filter.mp h).2.2.1
    change n ≤ high at hhi
    omega
  apply path_gap_deadline_lower_bound n _ _
    (pathWhiteGap_of_seed_hit_interval n blue support hcover low high) hz hl _ deadline hfinish
  intro x hx hb
  have hi := (Finset.mem_filter.mp hx).2
  have hB := (Finset.mem_sdiff.mp hb).1
  have hNot := (Finset.mem_sdiff.mp hb).2
  rcases hi.2.2 with hw | hs
  · exact hw hB
  · exact hNot (Finset.mem_filter.mpr ⟨hs, hi.1, hi.2.1⟩)

end FaultObservationResearch
