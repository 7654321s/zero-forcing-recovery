module

/- Mirror interval estimates using the proved path-reversal isomorphism. -/
public import «formalization-path-interval-upper»
public import «formalization-path-gap-one-sided»
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

theorem pathWhiteGap_reverse (n : ℕ) (white : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) :
    PathWhiteGap n (relabelColors (pathReverseEquiv n) white) := by
  classical
  intro x y hx hy hxy a ha b hb hax hyb
  have hx' : Fin.rev x ∉ white := by simpa [pathReverseEquiv] using hx
  have hy' : Fin.rev y ∉ white := by simpa [pathReverseEquiv] using hy
  have ha' : Fin.rev a ∈ white := by simpa [pathReverseEquiv] using ha
  have hb' : Fin.rev b ∈ white := by simpa [pathReverseEquiv] using hb
  apply hgap (Fin.rev y) (Fin.rev x) hy' hx' _ (Fin.rev b) hb' (Fin.rev a) ha' _ _
  all_goals
    simp only [Fin.val_rev]
    have := x.isLt
    have := y.isLt
    have := a.isLt
    have := b.isLt
    omega

theorem path_gap_right_deadline_lower_bound (n : ℕ) (white blue : Finset (Fin (n + 1)))
    (hgap : PathWhiteGap n white) (hright : white = ∅ ∨ Fin.last n ∈ white)
    (hzero : (0 : Fin (n + 1)) ∉ white) (hwhite : ∀ x ∈ white, x ∉ blue)
    (deadline : ℕ) (hfinish : FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj blue deadline) :
    white.card ≤ deadline := by
  classical
  let e := pathReverseEquiv n
  have hlast : e.symm (Fin.last n) = 0 := by
    apply Fin.ext
    change n + 1 - (n + 1) = 0
    omega
  have hleft : relabelColors e white = ∅ ∨ (0 : Fin (n + 1)) ∈ relabelColors e white := by
    rcases hright with he | he
    · left
      simp [he, relabelColors]
    · right
      simpa only [mem_relabelColors, e, pathReverseEquiv_symm_zero] using he
  have hn : Fin.last n ∉ relabelColors e white := by
    simpa only [mem_relabelColors, hlast] using hzero
  have hcol : ∀ x ∈ relabelColors e white, x ∉ relabelColors e blue := by
    intro x hx hb
    exact hwhite (e.symm x) ((mem_relabelColors _ _ _).mp hx) ((mem_relabelColors _ _ _).mp hb)
  have hf := (FinishesBy_relabel_iff e _ _ (fun x y => (pathReverseIso n).map_rel_iff) blue deadline).mpr hfinish
  have hle := path_gap_one_sided_deadline_lower_bound n _ _
    (pathWhiteGap_reverse n white hgap) hleft hn hcol deadline hf
  simpa only [relabelColors_card] using hle

theorem path_interval_suffix_deadline_lower_bound (n : ℕ) (blue support : Finset (Fin (n + 1)))
    (hcover : HitsPathSeeds n blue support) (low : ℕ) (hlow : 0 < low) (hln : low ≤ n)
    (deadline : ℕ)
    (hfinish : FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj
      (blue \ support.filter (fun x => low ≤ x.val ∧ x.val ≤ n)) deadline) :
    (PathWhiteInterval n blue support low n).card ≤ deadline := by
  classical
  have hn : Fin.last n ∈ PathWhiteInterval n blue support low n := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hln, le_rfl, ?_⟩
    by_cases hB : Fin.last n ∈ blue
    · exact Or.inr (hcover.2.1 hB)
    · exact Or.inl hB
  have hz : (0 : Fin (n + 1)) ∉ PathWhiteInterval n blue support low n := by
    intro h
    have hi := (Finset.mem_filter.mp h).2.1
    change low ≤ 0 at hi
    omega
  apply path_gap_right_deadline_lower_bound n _ _
    (pathWhiteGap_of_seed_hit_interval n blue support hcover low n) (Or.inr hn) hz _ deadline hfinish
  intro x hx hb
  have hi := (Finset.mem_filter.mp hx).2
  have hB := (Finset.mem_sdiff.mp hb).1
  have hNot := (Finset.mem_sdiff.mp hb).2
  rcases hi.2.2 with hw | hs
  · exact hw hB
  · exact hNot (Finset.mem_filter.mpr ⟨hs, hi.1, hi.2.1⟩)

theorem pathIntervalWhites_reverse (n : ℕ) (blue : Finset (Fin (n + 1)))
    (left right : Fin (n + 1)) :
    PathIntervalWhites n (relabelColors (pathReverseEquiv n) blue) (Fin.rev right) (Fin.rev left) =
      relabelColors (pathReverseEquiv n) (PathIntervalWhites n blue left right) := by
  classical
  ext x
  simp only [PathIntervalWhites, mem_relabelColors, Finset.mem_filter, Finset.mem_univ, true_and]
  change (Fin.rev right).val ≤ x.val ∧ x.val ≤ (Fin.rev left).val ∧ Fin.rev x ∉ blue ↔
    left.val ≤ (Fin.rev x).val ∧ (Fin.rev x).val ≤ right.val ∧ Fin.rev x ∉ blue
  have h1 : (Fin.rev right).val ≤ x.val ↔ (Fin.rev x).val ≤ right.val := by
    simpa only [Fin.rev_rev, Fin.le_def] using (Fin.rev_le_rev (i := right) (j := Fin.rev x))
  have h2 : x.val ≤ (Fin.rev left).val ↔ left.val ≤ (Fin.rev x).val := by
    simpa only [Fin.rev_rev, Fin.le_def] using (Fin.rev_le_rev (i := Fin.rev x) (j := left))
  rw [h1, h2]
  aesop

theorem pathLeftReady_reverse (n : ℕ) (blue : Finset (Fin (n + 1)))
    (left : Fin (n + 1)) (hready : PathLeftReady n blue left) :
    PathRightReady n (relabelColors (pathReverseEquiv n) blue) (Fin.rev left) := by
  classical
  constructor
  · apply (mem_relabelColors _ _ _).mpr
    change Fin.rev (Fin.rev left) ∈ blue
    simpa only [Fin.rev_rev] using hready.1
  · intro x ha hl
    have hAdj : (SimpleGraph.pathGraph (n + 1)).Adj left (Fin.rev x) := by
      have hh : (SimpleGraph.pathGraph (n + 1)).Adj
          ((pathReverseIso n) left) ((pathReverseIso n) (Fin.rev x)) := by
        change (SimpleGraph.pathGraph (n + 1)).Adj (Fin.rev left) (Fin.rev (Fin.rev x))
        simpa only [Fin.rev_rev] using ha
      exact (pathReverseIso n).map_rel_iff.mp hh
    have hLess : (Fin.rev x).val < left.val := by
      simp only [Fin.val_rev] at hl ⊢
      have := x.isLt
      have := left.isLt
      omega
    exact (mem_relabelColors _ _ _).mpr (hready.2 (Fin.rev x) hAdj hLess)

theorem path_interval_left_sided_upper (n : ℕ) (blue : Finset (Fin (n + 1)))
    (left right : Fin (n + 1)) (hleft : PathLeftReady n blue left) (deadline : ℕ)
    (hcount : (PathIntervalWhites n blue left right).card ≤ deadline) :
    ∀ x : Fin (n + 1), left.val ≤ x.val → x.val ≤ right.val →
      x ∈ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj blue deadline := by
  classical
  let e := pathReverseEquiv n
  have hc : (PathIntervalWhites n (relabelColors e blue) (Fin.rev right) (Fin.rev left)).card ≤ deadline := by
    rw [pathIntervalWhites_reverse, relabelColors_card]
    exact hcount
  have hf := path_interval_one_sided_upper n (relabelColors e blue)
    (Fin.rev right) (Fin.rev left) (pathLeftReady_reverse n blue left hleft) deadline hc
  intro x hxl hxr
  have hrev := hf (Fin.rev x) (by
    simp only [Fin.val_rev]
    have := x.isLt
    have := right.isLt
    omega) (by
    simp only [Fin.val_rev]
    have := x.isLt
    have := left.isLt
    omega)
  rw [← colorAfter_relabel e _ _ (fun a b => (pathReverseIso n).map_rel_iff) blue deadline] at hrev
  have hin : e.symm (Fin.rev x) ∈ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj blue deadline :=
    (mem_relabelColors _ _ _).mp hrev
  change Fin.rev (Fin.rev x) ∈ colorAfter (SimpleGraph.pathGraph (n + 1)).Adj blue deadline at hin
  simpa only [Fin.rev_rev] using hin

end FaultObservationResearch
