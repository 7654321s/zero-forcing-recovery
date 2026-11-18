module

/-
White nonleaf center with a blue leaf guard, and a nonadjacent leaf-pair center.
Draft until a recorded Lean build and axiom audit succeeds. This is a local
obstruction tool, not a full tree classification or a priority claim.
-/
public import «formalization-single-white-leaf»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem white_center_leaf_guard_one_loss_finishes_two (G : SimpleGraph V) (w y : V)
    (hyw : G.Adj y w) (hy : ∀ z, G.Adj y z → z = w)
    (hother : ∃ q, G.Adj w q ∧ q ≠ y)
    (hn : ∀ x, ∃ q, G.Adj x q) (x : V) :
    FinishesBy G.Adj (Finset.univ \ {w, x}) 2 := by
  classical
  have hfirst : w ∈ synchronousStep G.Adj (Finset.univ \ {w, x}) := by
    by_cases hxy : x = y
    · subst x
      obtain ⟨q, hwq, hqy⟩ := hother
      apply (mem_synchronousStep _ _ _).mpr
      refine Or.inr ⟨q, by simp [hwq.ne', hqy], hwq.symm, ?_⟩
      intro z hqz hz
      by_cases hzw : z = w
      · exact hzw
      · have hzy : z = y := by simpa [hzw] using hz
        subst z
        exact False.elim (hwq.ne' (hy q hqz.symm))
    · apply (mem_synchronousStep _ _ _).mpr
      refine Or.inr ⟨y, by simp [hyw.ne, Ne.symm hxy], hyw, ?_⟩
      intro z hyz _
      exact hy z hyz
  have hpair : ({x, w} : Finset V) = {w, x} := Finset.pair_comm x w
  have hf := two_white_finishes_two_of_first_recovery G x w (hn x) (by
    simpa only [hpair] using hfirst)
  simpa only [hpair] using hf

structure NonadjacentLeafCentersWitness {X : Type u} (G : SimpleGraph X) where
  connected : G.Connected
  whiteRoot : X
  guardLeaf : X
  pairCenter : X
  leafA : X
  leafB : X
  guard_adj : G.Adj guardLeaf whiteRoot
  guard_leaf : ∀ z, G.Adj guardLeaf z → z = whiteRoot
  other_neighbor : ∃ q, G.Adj whiteRoot q ∧ q ≠ guardLeaf
  centers_ne : whiteRoot ≠ pairCenter
  centers_nonadjacent : ¬ G.Adj whiteRoot pairCenter
  a_adj : G.Adj leafA pairCenter
  b_adj : G.Adj leafB pairCenter
  a_leaf : ∀ z, G.Adj leafA z → z = pairCenter
  b_leaf : ∀ z, G.Adj leafB z → z = pairCenter
  leaves_ne : leafA ≠ leafB

omit [Fintype V] [DecidableEq V] in
theorem nonadjacentLeafCenters_geometry (G : SimpleGraph V)
    (W : NonadjacentLeafCentersWitness G) :
    W.leafA ≠ W.whiteRoot ∧ W.leafB ≠ W.whiteRoot ∧
      W.guardLeaf ≠ W.leafA ∧ W.guardLeaf ≠ W.leafB := by
  have haw : W.leafA ≠ W.whiteRoot := by
    intro h
    exact W.centers_nonadjacent (h ▸ W.a_adj)
  have hbw : W.leafB ≠ W.whiteRoot := by
    intro h
    exact W.centers_nonadjacent (h ▸ W.b_adj)
  have hya : W.guardLeaf ≠ W.leafA := by
    intro h
    exact W.centers_ne (W.a_leaf W.whiteRoot (h ▸ W.guard_adj))
  have hyb : W.guardLeaf ≠ W.leafB := by
    intro h
    exact W.centers_ne (W.b_leaf W.whiteRoot (h ▸ W.guard_adj))
  exact ⟨haw, hbw, hya, hyb⟩

def nonadjacentLeafCentersBlue {G : SimpleGraph V}
    (W : NonadjacentLeafCentersWitness G) : Finset V := Finset.univ \ {W.whiteRoot}

def nonadjacentLeafCentersSupport {G : SimpleGraph V}
    (W : NonadjacentLeafCentersWitness G) : Finset V := {W.leafA, W.leafB}

theorem nonadjacentLeafCenters_global_deadline (G : SimpleGraph V)
    (W : NonadjacentLeafCentersWitness G) :
    RobustBy G.Adj (nonadjacentLeafCentersBlue W) (nonadjacentLeafCentersBlue W) 1 2 := by
  classical
  have : Nontrivial V := ⟨⟨W.leafA, W.leafB, W.leaves_ne⟩⟩
  intro loss _hsub hsize
  by_cases he : loss = ∅
  · subst loss
    simpa only [Finset.sdiff_empty] using
      FinishesBy_mono_time G.Adj (nonadjacentLeafCentersBlue W)
        (one_white_finishes_one G W.whiteRoot ⟨W.guardLeaf, W.guard_adj.symm⟩)
        (by omega : 1 ≤ 2)
  · have hcard : loss.card = 1 := by
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
    have heq : nonadjacentLeafCentersBlue W \ {x} = Finset.univ \ {W.whiteRoot, x} := by
      ext z
      simp [nonadjacentLeafCentersBlue, not_or]
    rw [heq]
    exact white_center_leaf_guard_one_loss_finishes_two G W.whiteRoot W.guardLeaf
      W.guard_adj W.guard_leaf W.other_neighbor
      W.connected.preconnected.exists_adj_of_nontrivial x

theorem nonadjacentLeafCenters_support_minimum (G : SimpleGraph V)
    (W : NonadjacentLeafCentersWitness G) :
    IsMinimumKilling G.Adj (nonadjacentLeafCentersBlue W) (nonadjacentLeafCentersSupport W) := by
  classical
  obtain ⟨haw, hbw, _, _⟩ := nonadjacentLeafCenters_geometry G W
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    simp only [nonadjacentLeafCentersSupport, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [nonadjacentLeafCentersBlue, haw]
    · simp [nonadjacentLeafCentersBlue, hbw]
  · apply same_center_leaf_pair_nonforcing G W.pairCenter W.leafA W.leafB W.leaves_ne
      W.a_adj W.b_adj W.a_leaf W.b_leaf
    · simp [nonadjacentLeafCentersSupport]
    · simp [nonadjacentLeafCentersSupport]
  · intro loss hsub hsmall
    have hc : (nonadjacentLeafCentersSupport W).card = 2 := by
      simp [nonadjacentLeafCentersSupport, W.leaves_ne]
    exact ⟨2, nonadjacentLeafCenters_global_deadline G W loss hsub (by omega)⟩

theorem nonadjacentLeafCenters_restricted_deadline (G : SimpleGraph V)
    (W : NonadjacentLeafCentersWitness G) :
    RobustBy G.Adj (nonadjacentLeafCentersBlue W) (nonadjacentLeafCentersSupport W) 1 1 := by
  classical
  intro loss hsub hsize
  let C := nonadjacentLeafCentersBlue W \ loss
  obtain ⟨_, _, hya, hyb⟩ := nonadjacentLeafCenters_geometry G W
  have hyBlue : W.guardLeaf ∈ C := by
    apply Finset.mem_sdiff.mpr
    refine ⟨by simp [nonadjacentLeafCentersBlue, W.guard_adj.ne], ?_⟩
    intro h
    have hs := hsub h
    simp only [nonadjacentLeafCentersSupport, Finset.mem_insert, Finset.mem_singleton] at hs
    exact hs.elim hya hyb
  have hcBlue : W.pairCenter ∈ C := by
    apply Finset.mem_sdiff.mpr
    refine ⟨by simp [nonadjacentLeafCentersBlue, W.centers_ne.symm], ?_⟩
    intro h
    have hs := hsub h
    simp only [nonadjacentLeafCentersSupport, Finset.mem_insert, Finset.mem_singleton] at hs
    exact hs.elim W.a_adj.ne' W.b_adj.ne'
  have hwhite : ∀ z, z ∉ C → z = W.whiteRoot ∨ z ∈ loss := by
    intro z hz
    by_cases hzw : z = W.whiteRoot
    · exact Or.inl hzw
    · right
      by_contra hnot
      exact hz (Finset.mem_sdiff.mpr ⟨by simp [nonadjacentLeafCentersBlue, hzw], hnot⟩)
  apply Finset.eq_univ_of_forall
  intro z
  by_cases hz : z ∈ C
  · exact subset_synchronousStep _ _ hz
  rcases hwhite z hz with rfl | hzl
  · apply (mem_synchronousStep _ _ _).mpr
    refine Or.inr ⟨W.guardLeaf, hyBlue, W.guard_adj, ?_⟩
    intro other ho _
    exact W.guard_leaf other ho
  · have hzadj : G.Adj W.pairCenter z := by
      have hs := hsub hzl
      simp only [nonadjacentLeafCentersSupport, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact W.a_adj.symm
      · exact W.b_adj.symm
    apply (mem_synchronousStep _ _ _).mpr
    refine Or.inr ⟨W.pairCenter, hcBlue, hzadj, ?_⟩
    intro other ho hw
    rcases hwhite other hw with rfl | hl
    · exact False.elim (W.centers_nonadjacent ho.symm)
    · exact (Finset.card_le_one_iff.mp hsize) hl hzl

theorem nonadjacentLeafCenters_not_support (G : SimpleGraph V)
    (W : NonadjacentLeafCentersWitness G) : ¬ EveryMinimumSupport G.Adj := by
  classical
  intro hU
  have hB : IsForcing G.Adj (nonadjacentLeafCentersBlue W) :=
    ⟨1, one_white_finishes_one G W.whiteRoot ⟨W.guardLeaf, W.guard_adj.symm⟩⟩
  have hglobal := (hU (nonadjacentLeafCentersBlue W) hB (nonadjacentLeafCentersSupport W)
    (nonadjacentLeafCenters_support_minimum G W) 1 1).mpr
    (nonadjacentLeafCenters_restricted_deadline G W)
  have hsub : {W.guardLeaf} ⊆ nonadjacentLeafCentersBlue W := by
    intro z hz
    have heq := Finset.mem_singleton.mp hz
    subst z
    simp [nonadjacentLeafCentersBlue, W.guard_adj.ne]
  have hf := hglobal {W.guardLeaf} hsub (by simp)
  have hlower := white_leaf_white_neighbor_completion_lower G W.guardLeaf W.whiteRoot W.guard_leaf
    (nonadjacentLeafCentersBlue W \ {W.guardLeaf}) (by simp) (by simp [nonadjacentLeafCentersBlue]) 1 hf
  omega

/- Direct hypotheses, without assuming a preconstructed witness record. -/
omit [Fintype V] [DecidableEq V] in
theorem leaf_center_other_neighbor_of_connected (G : SimpleGraph V) (hconn : G.Connected)
    (w y c : V) (hy : ∀ z, G.Adj y z → z = w)
    (hwc : w ≠ c) (hcy : c ≠ y) : ∃ q, G.Adj w q ∧ q ≠ y := by
  classical
  by_contra hnone
  have hall : ∀ q, G.Adj w q → q = y := by
    intro q hq
    by_contra hqy
    exact hnone ⟨q, hq, hqy⟩
  let S : Set V := {w, y}
  have hclosed : ∀ x ∈ S, ∀ z, G.Adj x z → z ∈ S := by
    intro x hx z hxz
    rcases hx with hx | hx
    · have hz := hall z (hx ▸ hxz)
      simp [S, hz]
    · have hx' : x = y := hx
      have hz := hy z (hx' ▸ hxz)
      simp [S, hz]
  have hfull := connected_neighbor_closed_eq_univ G hconn S w (by simp [S]) hclosed
  have hc : c ∈ S := by rw [hfull]; trivial
  rcases hc with hc | hc
  · exact hwc hc.symm
  · exact hcy hc

theorem connected_nonadjacent_leaf_centers_not_support
    (G : SimpleGraph V) (hconn : G.Connected) (w y c a b : V)
    (hyw : G.Adj y w) (hy : TreeLeaf G y)
    (hwc : w ≠ c) (hnonadj : ¬ G.Adj w c)
    (hab : a ≠ b) (hac : G.Adj a c) (ha : TreeLeaf G a)
    (hbc : G.Adj b c) (hb : TreeLeaf G b) : ¬ EveryMinimumSupport G.Adj := by
  have hyonly : ∀ z, G.Adj y z → z = w := by
    obtain ⟨q, _, hu⟩ := hy
    intro z hz
    exact (hu z hz).trans (hu w hyw).symm
  have hcy : c ≠ y := by
    intro h
    exact hnonadj (h.symm ▸ hyw.symm)
  let W : NonadjacentLeafCentersWitness G := {
    connected := hconn
    whiteRoot := w
    guardLeaf := y
    pairCenter := c
    leafA := a
    leafB := b
    guard_adj := hyw
    guard_leaf := hyonly
    other_neighbor := leaf_center_other_neighbor_of_connected G hconn w y c hyonly hwc hcy
    centers_ne := hwc
    centers_nonadjacent := hnonadj
    a_adj := hac
    b_adj := hbc
    a_leaf := by
      obtain ⟨q, _, hu⟩ := ha
      intro z hz
      exact (hu z hz).trans (hu c hac).symm
    b_leaf := by
      obtain ⟨q, _, hu⟩ := hb
      intro z hz
      exact (hu z hz).trans (hu c hbc).symm
    leaves_ne := hab }
  exact nonadjacentLeafCenters_not_support G W


end FaultObservationResearch
