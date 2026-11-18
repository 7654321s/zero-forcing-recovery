module

/-
Two-round recovery with one initially white leaf and one further loss.
This is a local propagation tool, not the full tree classification or an
originality claim. The current build record determines acceptance.
-/
public import «formalization-rooted-leaves»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem one_white_finishes_one (G : SimpleGraph V) (w : V)
    (hn : ∃ q, G.Adj w q) :
    FinishesBy G.Adj (Finset.univ \ {w}) 1 := by
  classical
  apply Finset.eq_univ_of_forall
  intro z
  by_cases hzw : z = w
  · subst z
    obtain ⟨q, hq⟩ := hn
    apply (mem_synchronousStep _ _ _).mpr
    refine Or.inr ⟨q, ?_, hq.symm, ?_⟩
    · simp [hq.ne']
    · intro other _ hw
      simpa using hw
  · exact subset_synchronousStep _ _ (by simp [hzw])

theorem two_white_finishes_two_of_first_recovery (G : SimpleGraph V) (w x : V)
    (hn : ∃ p, G.Adj w p)
    (hx : x ∈ synchronousStep G.Adj (Finset.univ \ {w, x})) :
    FinishesBy G.Adj (Finset.univ \ {w, x}) 2 := by
  classical
  let C : Finset V := Finset.univ \ {w, x}
  have hstep : ∀ z, z ≠ w → z ∈ synchronousStep G.Adj C := by
    intro z hzw
    by_cases hzx : z = x
    · simpa only [hzx] using hx
    · exact subset_synchronousStep _ _ (by simp [C, hzw, hzx])
  apply Finset.eq_univ_of_forall
  intro z
  by_cases hzw : z = w
  · subst z
    obtain ⟨p, hp⟩ := hn
    apply (mem_synchronousStep _ _ _).mpr
    refine Or.inr ⟨p, hstep p hp.ne', hp.symm, ?_⟩
    intro other _ hw
    by_contra hne
    exact hw (hstep other hne)
  · exact subset_synchronousStep _ _ (hstep z hzw)

theorem leaf_no_mate_has_other_neighbor (G : SimpleGraph V) (w root : V)
    (hn : ∀ x, ∃ y, G.Adj x y)
    (hmate : ∀ x, G.Adj root x → TreeLeaf G x → x = w)
    (x : V) (hxw : x ≠ w) : ∃ q, G.Adj x q ∧ q ≠ root := by
  classical
  by_contra hnone
  have hall : ∀ q, G.Adj x q → q = root := by
    intro q hq
    by_contra hqr
    exact hnone ⟨q, hq, hqr⟩
  obtain ⟨q, hq⟩ := hn x
  have hxr : G.Adj x root := hall q hq ▸ hq
  have hxleaf : TreeLeaf G x := ⟨root, hxr, hall⟩
  exact hxw (hmate x hxr.symm hxleaf)

theorem single_white_leaf_one_loss_finishes_two (G : SimpleGraph V) (w root : V)
    (hwr : G.Adj w root) (hleaf : ∀ z, G.Adj w z → z = root)
    (hroot : ∃ q, G.Adj root q ∧ q ≠ w)
    (hn : ∀ x, ∃ y, G.Adj x y)
    (hmate : ∀ x, G.Adj root x → TreeLeaf G x → x = w)
    (x : V) (hxw : x ≠ w) :
    FinishesBy G.Adj (Finset.univ \ {w, x}) 2 := by
  classical
  have hsource : ∃ q, G.Adj x q ∧ q ≠ w ∧ q ≠ x ∧ q ≠ root := by
    by_cases hxr : x = root
    · subst x
      obtain ⟨q, hq, hqw⟩ := hroot
      exact ⟨q, hq, hqw, hq.ne', hq.ne'⟩
    · obtain ⟨q, hq, hqr⟩ := leaf_no_mate_has_other_neighbor G w root hn hmate x hxw
      have hqw : q ≠ w := by
        intro heq
        subst q
        exact hxr (hleaf x hq.symm)
      exact ⟨q, hq, hqw, hq.ne', hqr⟩
  obtain ⟨q, hq, hqw, hqx, hqr⟩ := hsource
  apply two_white_finishes_two_of_first_recovery G w x ⟨root, hwr⟩
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨q, ?_, hq.symm, ?_⟩
  · simp [hqw, hqx]
  · intro other ho hw
    have hwhite : other = w ∨ other = x := by
      by_cases how : other = w
      · exact Or.inl how
      · apply Or.inr
        have himp : other ≠ w → other = x := by simpa using hw
        exact himp how
    rcases hwhite with rfl | hox
    · exact False.elim (hqr (hleaf q ho.symm))
    · exact hox


/- Neighbor-closed sets in a connected graph contain every vertex. This standard
   structural tool will also be used for exact tree-cover arguments. -/
omit [Fintype V] [DecidableEq V] in
theorem connected_neighbor_closed_eq_univ (G : SimpleGraph V) (hG : G.Connected)
    (S : Set V) (root : V) (hr : root ∈ S)
    (hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S) : S = Set.univ := by
  have hwalk : ∀ {x y : V}, G.Walk x y → x ∈ S → y ∈ S := by
    intro x y walk
    induction walk with
    | nil => exact fun hx => hx
    | @cons a b c h walk ih =>
      intro ha
      exact ih (hclosed a ha b h)
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨walk⟩ := hG.preconnected root z
  exact hwalk walk hr

structure UniqueLeafPairWitness {X : Type u} (G : SimpleGraph X) where
  connected : G.Connected
  white : X
  root : X
  center : X
  leafA : X
  leafB : X
  white_adj : G.Adj white root
  white_leaf : ∀ z, G.Adj white z → z = root
  only_leaf_at_root : ∀ x, G.Adj root x → TreeLeaf G x → x = white
  a_adj : G.Adj leafA center
  b_adj : G.Adj leafB center
  a_leaf : ∀ z, G.Adj leafA z → z = center
  b_leaf : ∀ z, G.Adj leafB z → z = center
  leaves_ne : leafA ≠ leafB

omit [Fintype V] [DecidableEq V] in
theorem uniqueLeafPair_geometry (G : SimpleGraph V) (W : UniqueLeafPairWitness G) :
    W.white ≠ W.root ∧ W.center ≠ W.root ∧ W.center ≠ W.white ∧
      W.leafA ≠ W.white ∧ W.leafB ≠ W.white ∧ W.root ≠ W.leafA ∧ W.root ≠ W.leafB := by
  have hcr : W.center ≠ W.root := by
    intro h
    have ha := W.only_leaf_at_root W.leafA (h ▸ W.a_adj.symm)
      ⟨W.center, W.a_adj, W.a_leaf⟩
    have hb := W.only_leaf_at_root W.leafB (h ▸ W.b_adj.symm)
      ⟨W.center, W.b_adj, W.b_leaf⟩
    exact W.leaves_ne (ha.trans hb.symm)
  have hcw : W.center ≠ W.white := by
    intro h
    have ha := W.white_leaf W.leafA (h ▸ W.a_adj.symm)
    have hb := W.white_leaf W.leafB (h ▸ W.b_adj.symm)
    exact W.leaves_ne (ha.trans hb.symm)
  have haw : W.leafA ≠ W.white := by
    intro h
    exact hcr (W.white_leaf W.center (h ▸ W.a_adj))
  have hbw : W.leafB ≠ W.white := by
    intro h
    exact hcr (W.white_leaf W.center (h ▸ W.b_adj))
  have hra : W.root ≠ W.leafA := by
    intro h
    exact hcw (W.a_leaf W.white (h ▸ W.white_adj.symm)).symm
  have hrb : W.root ≠ W.leafB := by
    intro h
    exact hcw (W.b_leaf W.white (h ▸ W.white_adj.symm)).symm
  exact ⟨W.white_adj.ne, hcr, hcw, haw, hbw, hra, hrb⟩

omit [Fintype V] [DecidableEq V] in
theorem uniqueLeafPair_recovery_data (G : SimpleGraph V) (W : UniqueLeafPairWitness G) :
    (∀ x, ∃ y, G.Adj x y) ∧ (∃ q, G.Adj W.root q ∧ q ≠ W.white) := by
  classical
  have : Nontrivial V := ⟨⟨W.leafA, W.leafB, W.leaves_ne⟩⟩
  refine ⟨W.connected.preconnected.exists_adj_of_nontrivial, ?_⟩
  by_contra hnone
  have hall : ∀ q, G.Adj W.root q → q = W.white := by
    intro q hq
    by_contra hne
    exact hnone ⟨q, hq, hne⟩
  let S : Set V := {W.white, W.root}
  have hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S := by
    intro x hx y hxy
    rcases hx with hx | hx
    · have hxy' : G.Adj W.white y := hx ▸ hxy
      have hy := W.white_leaf y hxy'
      simp [S, hy]
    · have hx' : x = W.root := hx
      have hy := hall y (hx' ▸ hxy)
      simp [S, hy]
  have hfull := connected_neighbor_closed_eq_univ G W.connected S W.white (by simp [S]) hclosed
  have hc : W.center ∈ S := by rw [hfull]; trivial
  have hgeo := uniqueLeafPair_geometry G W
  rcases hc with hc | hc
  · exact hgeo.2.2.1 hc
  · exact hgeo.2.1 hc

def uniqueLeafPairBlue {G : SimpleGraph V} (W : UniqueLeafPairWitness G) : Finset V :=
  Finset.univ \ {W.white}

def uniqueLeafPairSupport {G : SimpleGraph V} (W : UniqueLeafPairWitness G) : Finset V :=
  {W.leafA, W.leafB}

theorem same_center_leaf_pair_stalled (G : SimpleGraph V) (v a b : V) (hab : a ≠ b)
    (hav : G.Adj a v) (hbv : G.Adj b v)
    (ha : ∀ z, G.Adj a z → z = v) (hb : ∀ z, G.Adj b z → z = v) :
    synchronousStep G.Adj (Finset.univ \ {a, b}) = Finset.univ \ {a, b} := by
  classical
  apply le_antisymm
  · intro target ht
    rcases (mem_synchronousStep _ _ _).mp ht with hold | ⟨source, _, hadj, hu⟩
    · exact hold
    by_cases htarget : target ∈ Finset.univ \ {a, b}
    · exact htarget
    have hcases : target = a ∨ target = b := by
      by_cases hta : target = a
      · exact Or.inl hta
      · apply Or.inr
        have himp : target ≠ a → target = b := by simpa using htarget
        exact himp hta
    rcases hcases with rfl | rfl
    · have hs := ha source hadj.symm
      subst source
      have heq := hu b hbv.symm (by simp)
      exact False.elim (hab heq.symm)
    · have hs := hb source hadj.symm
      subst source
      have heq := hu a hav.symm (by simp)
      exact False.elim (hab heq)
  · exact subset_synchronousStep _ _

theorem same_center_leaf_pair_nonforcing (G : SimpleGraph V) (v a b : V) (hab : a ≠ b)
    (hav : G.Adj a v) (hbv : G.Adj b v)
    (ha : ∀ z, G.Adj a z → z = v) (hb : ∀ z, G.Adj b z → z = v)
    (C : Finset V) (hwa : a ∉ C) (hwb : b ∉ C) : ¬ IsForcing G.Adj C := by
  classical
  have hsub : C ⊆ Finset.univ \ {a, b} := by
    intro z hz
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or]
    exact ⟨fun h => hwa (h ▸ hz), fun h => hwb (h ▸ hz)⟩
  intro hf
  obtain ⟨t, ht⟩ := IsForcing_mono G.Adj hsub hf
  have hdone : colorAfter G.Adj (Finset.univ \ {a, b}) t = Finset.univ := ht
  rw [colorAfter_of_fixed _ _ (same_center_leaf_pair_stalled G v a b hab hav hbv ha hb) t] at hdone
  have hm : a ∈ Finset.univ \ {a, b} := by rw [hdone]; exact Finset.mem_univ _
  simp at hm

theorem uniqueLeafPair_global_deadline (G : SimpleGraph V) (W : UniqueLeafPairWitness G) :
    RobustBy G.Adj (uniqueLeafPairBlue W) (uniqueLeafPairBlue W) 1 2 := by
  classical
  intro loss hsub hsize
  by_cases he : loss = ∅
  · subst loss
    simpa only [Finset.sdiff_empty] using
      FinishesBy_mono_time G.Adj (uniqueLeafPairBlue W)
        (one_white_finishes_one G W.white ⟨W.root, W.white_adj⟩) (by omega : 1 ≤ 2)
  · have hcard : loss.card = 1 := by
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
    have hx : x ≠ W.white := by
      have hm := hsub (Finset.mem_singleton_self x)
      simpa [uniqueLeafPairBlue] using hm
    have heq : uniqueLeafPairBlue W \ {x} = Finset.univ \ {W.white, x} := by
      ext z
      simp [uniqueLeafPairBlue, not_or]
    rw [heq]
    have hdata := uniqueLeafPair_recovery_data G W
    exact single_white_leaf_one_loss_finishes_two G W.white W.root W.white_adj W.white_leaf
      hdata.2 hdata.1 W.only_leaf_at_root x hx

theorem uniqueLeafPair_support_minimum (G : SimpleGraph V) (W : UniqueLeafPairWitness G) :
    IsMinimumKilling G.Adj (uniqueLeafPairBlue W) (uniqueLeafPairSupport W) := by
  classical
  have hgeo := uniqueLeafPair_geometry G W
  have haw := hgeo.2.2.2.1
  have hbw := hgeo.2.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    simp only [uniqueLeafPairSupport, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [uniqueLeafPairBlue, haw]
    · simp [uniqueLeafPairBlue, hbw]
  · apply same_center_leaf_pair_nonforcing G W.center W.leafA W.leafB W.leaves_ne
      W.a_adj W.b_adj W.a_leaf W.b_leaf
    · simp [uniqueLeafPairSupport]
    · simp [uniqueLeafPairSupport]
  · intro loss hsub hsmall
    have hcard : (uniqueLeafPairSupport W).card = 2 := by
      simp [uniqueLeafPairSupport, W.leaves_ne]
    have hsize : loss.card ≤ 1 := by omega
    exact ⟨2, uniqueLeafPair_global_deadline G W loss hsub hsize⟩

theorem uniqueLeafPair_restricted_deadline (G : SimpleGraph V) (W : UniqueLeafPairWitness G) :
    RobustBy G.Adj (uniqueLeafPairBlue W) (uniqueLeafPairSupport W) 1 1 := by
  classical
  intro loss hsub hsize
  let C := uniqueLeafPairBlue W \ loss
  rcases uniqueLeafPair_geometry G W with ⟨hwr, hcr, hcw, _, _, hra, hrb⟩
  have hrootBlue : W.root ∈ C := by
    apply Finset.mem_sdiff.mpr
    refine ⟨by simp [uniqueLeafPairBlue, hwr.symm], ?_⟩
    intro hm
    have hs := hsub hm
    simp only [uniqueLeafPairSupport, Finset.mem_insert, Finset.mem_singleton] at hs
    exact hs.elim hra hrb
  have hcenterBlue : W.center ∈ C := by
    apply Finset.mem_sdiff.mpr
    refine ⟨by simp [uniqueLeafPairBlue, hcw], ?_⟩
    intro hm
    have hs := hsub hm
    simp only [uniqueLeafPairSupport, Finset.mem_insert, Finset.mem_singleton] at hs
    exact hs.elim W.a_adj.ne' W.b_adj.ne'
  have hwhite : ∀ z, z ∉ C → z = W.white ∨ z ∈ loss := by
    intro z hz
    by_cases hzw : z = W.white
    · exact Or.inl hzw
    · right
      by_contra hnot
      exact hz (Finset.mem_sdiff.mpr ⟨by simp [uniqueLeafPairBlue, hzw], hnot⟩)
  apply Finset.eq_univ_of_forall
  intro z
  by_cases hz : z ∈ C
  · exact subset_synchronousStep _ _ hz
  rcases hwhite z hz with rfl | hzl
  · apply (mem_synchronousStep _ _ _).mpr
    refine Or.inr ⟨W.root, hrootBlue, W.white_adj.symm, ?_⟩
    intro other ho hw
    rcases hwhite other hw with heq | hl
    · exact heq
    · have hs := hsub hl
      simp only [uniqueLeafPairSupport, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact False.elim (hcr (W.a_leaf W.root ho.symm).symm)
      · exact False.elim (hcr (W.b_leaf W.root ho.symm).symm)
  · have hzadj : G.Adj W.center z := by
      have hs := hsub hzl
      simp only [uniqueLeafPairSupport, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact W.a_adj.symm
      · exact W.b_adj.symm
    apply (mem_synchronousStep _ _ _).mpr
    refine Or.inr ⟨W.center, hcenterBlue, hzadj, ?_⟩
    intro other ho hw
    rcases hwhite other hw with rfl | hl
    · exact False.elim (hcr (W.white_leaf W.center ho.symm))
    · exact (Finset.card_le_one_iff.mp hsize) hl hzl

theorem white_leaf_white_neighbor_completion_lower (G : SimpleGraph V) (w root : V)
    (hleaf : ∀ z, G.Adj w z → z = root) (C : Finset V)
    (hw : w ∉ C) (hr : root ∉ C) (t : ℕ) (hf : FinishesBy G.Adj C t) : 2 ≤ t := by
  classical
  have hfirst : w ∉ synchronousStep G.Adj C := by
    intro h
    rcases (mem_synchronousStep _ _ _).mp h with h | ⟨source, hs, ha, _⟩
    · exact hw h
    · exact hr (hleaf source ha.symm ▸ hs)
  by_contra hsmall
  have ht : t = 0 ∨ t = 1 := by omega
  have hm : w ∈ colorAfter G.Adj C t := by rw [hf]; exact Finset.mem_univ _
  rcases ht with rfl | rfl
  · exact hw hm
  · exact hfirst hm

theorem uniqueLeafPair_not_support (G : SimpleGraph V) (W : UniqueLeafPairWitness G) :
    ¬ EveryMinimumSupport G.Adj := by
  classical
  intro hU
  have hB : IsForcing G.Adj (uniqueLeafPairBlue W) :=
    ⟨1, one_white_finishes_one G W.white ⟨W.root, W.white_adj⟩⟩
  have hglobal := (hU (uniqueLeafPairBlue W) hB (uniqueLeafPairSupport W)
    (uniqueLeafPair_support_minimum G W) 1 1).mpr (uniqueLeafPair_restricted_deadline G W)
  have hsub : {W.root} ⊆ uniqueLeafPairBlue W := by
    intro z hz
    have heq := Finset.mem_singleton.mp hz
    subst z
    simp [uniqueLeafPairBlue, W.white_adj.ne']
  have hf := hglobal {W.root} hsub (by simp)
  have hlower := white_leaf_white_neighbor_completion_lower G W.white W.root W.white_leaf
    (uniqueLeafPairBlue W \ {W.root}) (by simp [uniqueLeafPairBlue]) (by simp) 1 hf
  omega



/- Public local-pattern statement. Connected graphs are allowed to have cycles;
   applying it to a tree only uses that the tree is connected. -/
theorem connected_leaf_pair_single_leaf_center_not_support
    (G : SimpleGraph V) (hconn : G.Connected) (root center w a b : V)
    (hwr : G.Adj w root) (hw : TreeLeaf G w)
    (hsingle : ∀ x, G.Adj root x → TreeLeaf G x → x = w)
    (hab : a ≠ b) (hac : G.Adj a center) (ha : TreeLeaf G a)
    (hbc : G.Adj b center) (hb : TreeLeaf G b) :
    ¬ EveryMinimumSupport G.Adj := by
  let W : UniqueLeafPairWitness G := {
    connected := hconn
    white := w
    root := root
    center := center
    leafA := a
    leafB := b
    white_adj := hwr
    white_leaf := by
      obtain ⟨q, _, hu⟩ := hw
      intro z hz
      exact (hu z hz).trans (hu root hwr).symm
    only_leaf_at_root := hsingle
    a_adj := hac
    b_adj := hbc
    a_leaf := by
      obtain ⟨q, _, hu⟩ := ha
      intro z hz
      exact (hu z hz).trans (hu center hac).symm
    b_leaf := by
      obtain ⟨q, _, hu⟩ := hb
      intro z hz
      exact (hu z hz).trans (hu center hbc).symm
    leaves_ne := hab }
  exact uniqueLeafPair_not_support G W


end FaultObservationResearch
