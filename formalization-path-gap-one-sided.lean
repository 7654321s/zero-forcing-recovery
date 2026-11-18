module

/-
One-ended white-gap dynamics and the endpoint interval lower bound.
The arbitrary-B every-minimum-support path theorem is still a separate target.
-/
public import «formalization-path-gap»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

theorem path_gap_zero_step_subset (n : ℕ) (white : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hne : white.Nonempty)
    (hz : (0 : Fin (n + 1)) ∈ white) :
    synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ white) ⊆
      (Finset.univ \ white) ∪ {white.max' hne} := by
  classical
  let m := white.max' hne
  have hm : m ∈ white := white.max'_mem hne
  intro target ht
  by_cases hold : target ∈ Finset.univ \ white
  · exact Finset.mem_union.mpr (Or.inl hold)
  have htW : target ∈ white := by simpa using hold
  have htLe : target.val ≤ m.val := white.le_max' target htW
  rcases (mem_synchronousStep _ _ _).mp ht with h | ⟨source, hs, hadj, hu⟩
  · exact False.elim (hold h)
  · have hsNot : source ∉ white := (Finset.mem_sdiff.mp hs).2
    by_cases hright : m.val < source.val
    · have heq : target = m := by
        apply Fin.ext
        rcases SimpleGraph.pathGraph_adj.mp hadj with h | h <;> omega
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr heq))
    · have hs0 : 0 < source.val := by
        have hsNe : source.val ≠ 0 := by
          intro h
          have heq : source = 0 := Fin.ext h
          exact hsNot (by rwa [heq])
        omega
      have hsNeM : source.val ≠ m.val := by
        intro h
        have heq : source = m := Fin.ext h
        exact hsNot (by rwa [heq])
      have hsm : source.val < m.val := by omega
      have hsn : source.val < n := by have := m.isLt; omega
      let left : Fin (n + 1) := ⟨source.val - 1, by have := source.isLt; omega⟩
      let right : Fin (n + 1) := ⟨source.val + 1, by omega⟩
      have hleftEq : left.val + 1 = source.val := by dsimp [left]; omega
      have hleftAdj := SimpleGraph.pathGraph_adj.mpr (Or.inr hleftEq)
      have hrightAdj := SimpleGraph.pathGraph_adj.mpr (Or.inl (show source.val + 1 = right.val from rfl))
      have hleftW := path_gap_blue_neighbor_white n white hgap source 0 m hsNot hz hm
        (by change 0 < source.val; exact hs0) hsm left hleftAdj
      have hrightW := path_gap_blue_neighbor_white n white hgap source 0 m hsNot hz hm
        (by change 0 < source.val; exact hs0) hsm right hrightAdj
      have hl := hu left hleftAdj (by simp [hleftW])
      have hr := hu right hrightAdj (by simp [hrightW])
      have hv := congrArg Fin.val (hl.trans hr.symm)
      change source.val - 1 = source.val + 1 at hv
      omega

theorem path_gap_zero_step (n : ℕ) (white : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hne : white.Nonempty)
    (hz : (0 : Fin (n + 1)) ∈ white) (hlast : Fin.last n ∉ white) :
    synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ white) =
      Finset.univ \ white.erase (white.max' hne) := by
  classical
  have hmax := path_max_loss_mem_step n white hne hlast
  have hstep : synchronousStep (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ white) =
      (Finset.univ \ white) ∪ {white.max' hne} := by
    apply le_antisymm (path_gap_zero_step_subset n white hgap hne hz)
    intro x hx
    rcases Finset.mem_union.mp hx with hold | hext
    · exact subset_synchronousStep _ _ hold
    · have heq := Finset.mem_singleton.mp hext
      simpa only [heq] using hmax
  rw [hstep]
  ext x
  by_cases heq : x = white.max' hne <;> simp [heq]

theorem pathWhiteGap_erase_max (n : ℕ) (white : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hne : white.Nonempty) :
    PathWhiteGap n (white.erase (white.max' hne)) := by
  classical
  intro x y hx hy hxy a ha b hb hax hyb
  have haW := (Finset.mem_erase.mp ha).2
  have hbW := (Finset.mem_erase.mp hb).2
  have hle : b.val ≤ (white.max' hne).val := white.le_max' b hbW
  have hxNe : x ≠ white.max' hne := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  have hyNe : y ≠ white.max' hne := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  have hxW : x ∉ white := fun h => hx (Finset.mem_erase.mpr ⟨hxNe, h⟩)
  have hyW : y ∉ white := fun h => hy (Finset.mem_erase.mpr ⟨hyNe, h⟩)
  exact hgap x y hxW hyW hxy a haW b hbW hax hyb

theorem path_gap_zero_persists_or_empty (n : ℕ) (white : Finset (Fin (n + 1)))
    (hne : white.Nonempty) (hz : (0 : Fin (n + 1)) ∈ white) :
    white.erase (white.max' hne) = ∅ ∨
      (0 : Fin (n + 1)) ∈ white.erase (white.max' hne) := by
  classical
  by_cases hempty : white.erase (white.max' hne) = ∅
  · exact Or.inl hempty
  · right
    refine Finset.mem_erase.mpr ⟨?_, hz⟩
    intro heq
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hmaxX := (Finset.mem_erase.mp hx).1
    have hxW := (Finset.mem_erase.mp hx).2
    have hle : x.val ≤ (white.max' hne).val := white.le_max' x hxW
    have hv := congrArg Fin.val heq
    have hxEq : x = white.max' hne := by
      apply Fin.ext
      change (0 : ℕ) = (white.max' hne).val at hv
      omega
    exact hmaxX hxEq

theorem path_gap_one_sided_finishes_iff (n : ℕ) (white : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hleft : white = ∅ ∨ (0 : Fin (n + 1)) ∈ white)
    (hlast : Fin.last n ∉ white) (deadline : ℕ) :
    FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ white) deadline ↔
      white.card ≤ deadline := by
  classical
  have general : ∀ m : ℕ, ∀ W : Finset (Fin (n + 1)), W.card = m →
      PathWhiteGap n W → (W = ∅ ∨ (0 : Fin (n + 1)) ∈ W) → Fin.last n ∉ W → ∀ t : ℕ,
      FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ W) t ↔ W.card ≤ t := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro W hcard hg hz hl t
      by_cases hempty : W = ∅
      · subst W
        simp [FinishesBy]
      · have hne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        have hzero : (0 : Fin (n + 1)) ∈ W := hz.resolve_left hempty
        have hpos : 0 < W.card := Finset.card_pos.mpr hne
        cases t with
        | zero =>
          constructor
          · intro hf
            have hx : W.max' hne ∈ Finset.univ \ W := by
              change Finset.univ \ W = Finset.univ at hf
              rw [hf]
              exact Finset.mem_univ _
            exact False.elim ((Finset.mem_sdiff.mp hx).2 (W.max'_mem hne))
          · intro h
            omega
        | succ t =>
          let S := W.erase (W.max' hne)
          have hsCard : S.card + 1 = W.card := by
            dsimp [S]
            rw [Finset.card_erase_of_mem (W.max'_mem hne)]
            omega
          have hSgap : PathWhiteGap n S := pathWhiteGap_erase_max n W hg hne
          have hSleft : S = ∅ ∨ (0 : Fin (n + 1)) ∈ S :=
            path_gap_zero_persists_or_empty n W hne hzero
          have hSl : Fin.last n ∉ S := fun h => hl ((Finset.mem_erase.mp h).2)
          have hshift := colorAfter_add (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ W) 1 t
          change colorAfter _ _ (1 + t) = colorAfter _ (synchronousStep _ (Finset.univ \ W)) t at hshift
          rw [Nat.add_comm 1 t, path_gap_zero_step n W hg hne hzero hl] at hshift
          change colorAfter _ _ (t + 1) = Finset.univ ↔ W.card ≤ t + 1
          rw [hshift]
          change FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj (Finset.univ \ S) t ↔ W.card ≤ t + 1
          rw [ih S.card (by omega) S rfl hSgap hSleft hSl t]
          omega
  exact general white.card white rfl hgap hleft hlast deadline

theorem path_gap_one_sided_deadline_lower_bound (n : ℕ) (white blue : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hleft : white = ∅ ∨ (0 : Fin (n + 1)) ∈ white)
    (hlast : Fin.last n ∉ white) (hwhite : ∀ x ∈ white, x ∉ blue)
    (deadline : ℕ) (hfinish : FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj blue deadline) :
    white.card ≤ deadline := by
  classical
  have hsub : blue ⊆ Finset.univ \ white := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hw => hwhite x hw hx⟩
  exact (path_gap_one_sided_finishes_iff n white hgap hleft hlast deadline).mp
    (FinishesBy_mono_blue _ hsub hfinish)

theorem path_interval_end_deadline_lower_bound (n : ℕ) (blue support : Finset (Fin (n + 1)))
    (hcover : HitsPathSeeds n blue support) (high : ℕ) (hhigh : high < n) (deadline : ℕ)
    (hfinish : FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj
      (blue \ support.filter (fun x => 0 ≤ x.val ∧ x.val ≤ high)) deadline) :
    (PathWhiteInterval n blue support 0 high).card ≤ deadline := by
  classical
  have hz : (0 : Fin (n + 1)) ∈ PathWhiteInterval n blue support 0 high := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · change 0 ≤ (0 : ℕ)
      omega
    · change 0 ≤ high
      omega
    · by_cases hB : (0 : Fin (n + 1)) ∈ blue
      · exact Or.inr (hcover.1 hB)
      · exact Or.inl hB
  have hl : Fin.last n ∉ PathWhiteInterval n blue support 0 high := by
    intro h
    have hhi := (Finset.mem_filter.mp h).2.2.1
    change n ≤ high at hhi
    omega
  apply path_gap_one_sided_deadline_lower_bound n _ _
    (pathWhiteGap_of_seed_hit_interval n blue support hcover 0 high) (Or.inr hz) hl _ deadline hfinish
  intro x hx hb
  have hi := (Finset.mem_filter.mp hx).2
  have hB := (Finset.mem_sdiff.mp hb).1
  have hNot := (Finset.mem_sdiff.mp hb).2
  rcases hi.2.2 with hw | hs
  · exact hw hB
  · exact hNot (Finset.mem_filter.mpr ⟨hs, hi.1, hi.2.1⟩)

end FaultObservationResearch
