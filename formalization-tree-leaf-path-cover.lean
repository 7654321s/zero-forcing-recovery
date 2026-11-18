module

/-
Standard finite-tree structural tools for the pending exhaustion argument.
Unchecked draft until a successful compiler/axiom record is available.
Maximal-path reasoning is established graph theory, not a novelty claim.
-/
public import «formalization-nonadjacent-leaf-centers»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem finite_maximal_path_through_vertex (G : SimpleGraph V) (z : V) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ z ∈ p.support ∧
      ∀ (a' b' : V) (q : G.Walk a' b'), q.IsPath → z ∈ q.support → q.length ≤ p.length := by
  classical
  let s : Set ℕ := {n | ∃ (a b : V) (p : G.Walk a b),
    p.IsPath ∧ z ∈ p.support ∧ p.length = n}
  have hfinite : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, _, hn⟩ => hn ▸ hp.isTrail.length_le_card_edgeFinset
  obtain ⟨_, ⟨⟨a, b, p, hp, hz, hpn⟩, hmax⟩⟩ :=
    hfinite.exists_maximal ⟨0, ⟨z, z, Walk.nil, by simp, by simp, rfl⟩⟩
  refine ⟨a, b, p, hp, hz, ?_⟩
  intro a' b' q hq hzq
  have h := hmax ⟨a', b', q, hq, hzq, rfl⟩
  omega

theorem finite_tree_vertex_on_leaf_path [Nontrivial V] (G : SimpleGraph V)
    (hG : G.IsTree) (z : V) :
    ∃ (a b : V) (p : G.Walk a b),
      p.IsPath ∧ TreeLeaf G a ∧ TreeLeaf G b ∧ z ∈ p.support := by
  classical
  obtain ⟨a, b, p, hp, hz, hmax⟩ := finite_maximal_path_through_vertex G z
  have hpos : 1 ≤ p.length := by
    obtain ⟨q, hq⟩ := hG.connected.preconnected.exists_adj_of_nontrivial z
    have h := hmax z q hq.toWalk (IsPath.of_adj hq) hq.toWalk.start_mem_support
    simpa using h
  have hnil : ¬ p.Nil := by
    intro h
    have hzero := length_eq_zero_iff.mpr h
    omega
  refine ⟨a, b, p, hp, ?_, ?_, hz⟩
  · refine ⟨p.snd, p.adj_snd hnil, ?_⟩
    intro x hax
    have hx : x ∈ p.support := by
      by_contra hnot
      have hnew : (p.cons hax.symm).IsPath := hp.cons hnot
      have h := hmax x b (p.cons hax.symm) hnew
        (p.support_subset_support_cons hax.symm hz)
      simp only [length_cons] at h
      omega
    exact hG.isAcyclic.eq_snd_of_adj_start hp hax hx
  · refine ⟨p.penultimate, (p.adj_penultimate hnil).symm, ?_⟩
    intro x hbx
    have hx : x ∈ p.support := by
      by_contra hnot
      have hnew : (p.concat hbx).IsPath := hp.concat hnot hbx
      have h := hmax a x (p.concat hbx) hnew
        (p.support_subset_support_concat hbx hz)
      simp only [length_concat] at h
      omega
    exact hG.isAcyclic.eq_penultimate_of_adj_end hp hbx hx

def TreeLeafParent (G : SimpleGraph V) (r : V) : Prop :=
  ∃ y, G.Adj y r ∧ TreeLeaf G y

def TreeLeafPairCenter (G : SimpleGraph V) (c : V) : Prop :=
  ∃ a b, a ≠ b ∧ G.Adj a c ∧ TreeLeaf G a ∧ G.Adj b c ∧ TreeLeaf G b

theorem support_cherry_leaf_parent_second_leaf (G : SimpleGraph V) (hconn : G.Connected)
    (hU : EveryMinimumSupport G.Adj) (hcherry : ∃ c, TreeLeafPairCenter G c)
    (r y : V) (hyr : G.Adj y r) (hy : TreeLeaf G y) :
    ∃ x, G.Adj x r ∧ TreeLeaf G x ∧ x ≠ y := by
  classical
  by_contra hnone
  have hsingle : ∀ x, G.Adj r x → TreeLeaf G x → x = y := by
    intro x hrx hx
    by_contra hxy
    exact hnone ⟨x, hrx.symm, hx, hxy⟩
  obtain ⟨c, a, b, hab, hac, ha, hbc, hb⟩ := hcherry
  exact (connected_leaf_pair_single_leaf_center_not_support G hconn r c y a b
    hyr hy hsingle hab hac ha hbc hb) hU

theorem support_cherry_leaf_parent_has_pair (G : SimpleGraph V) (hconn : G.Connected)
    (hU : EveryMinimumSupport G.Adj) (hcherry : ∃ c, TreeLeafPairCenter G c)
    (r : V) (hr : TreeLeafParent G r) : TreeLeafPairCenter G r := by
  obtain ⟨y, hyr, hy⟩ := hr
  obtain ⟨x, hxr, hx, hxy⟩ := support_cherry_leaf_parent_second_leaf G hconn hU hcherry r y hyr hy
  exact ⟨y, x, hxy.symm, hyr, hy, hxr, hx⟩

theorem support_cherry_leaf_parents_clique (G : SimpleGraph V) (hconn : G.Connected)
    (hU : EveryMinimumSupport G.Adj) (hcherry : ∃ c, TreeLeafPairCenter G c)
    (r c : V) (hr : TreeLeafParent G r) (hc : TreeLeafParent G c) (hrc : r ≠ c) :
    G.Adj r c := by
  classical
  by_contra hnonadj
  obtain ⟨y, hyr, hy⟩ := hr
  obtain ⟨a, b, hab, hac, ha, hbc, hb⟩ := support_cherry_leaf_parent_has_pair G hconn hU hcherry c hc
  exact (connected_nonadjacent_leaf_centers_not_support G hconn r y c a b
    hyr hy hrc hnonadj hab hac ha hbc hb) hU

omit [Fintype V] [DecidableEq V] in
theorem leaf_pair_center_not_leaf (G : SimpleGraph V) (c : V)
    (hc : TreeLeafPairCenter G c) : ¬ TreeLeaf G c := by
  obtain ⟨a, b, hab, hac, _, hbc, _⟩ := hc
  intro hleaf
  obtain ⟨q, _, hq⟩ := hleaf
  exact hab ((hq a hac.symm).trans (hq b hbc.symm).symm)

theorem finite_tree_leaf_parent_clique_cover [Nontrivial V] (G : SimpleGraph V)
    (hG : G.IsTree)
    (hpair : ∀ r, TreeLeafParent G r → TreeLeafPairCenter G r)
    (hclique : ∀ r c, TreeLeafParent G r → TreeLeafParent G c → r ≠ c → G.Adj r c)
    (z : V) : TreeLeaf G z ∨ TreeLeafParent G z := by
  classical
  obtain ⟨a, b, p, hp, ha, hb, hz⟩ := finite_tree_vertex_on_leaf_path G hG z
  by_cases hab : a = b
  · have hnil : p.Nil := hp.nil_iff_eq.mpr hab
    rw [nil_iff_support_eq.mp hnil] at hz
    have hza : z = a := List.mem_singleton.mp hz
    exact Or.inl (hza.symm ▸ ha)
  have haCopy := ha
  have hbCopy := hb
  obtain ⟨r, har, _⟩ := haCopy
  obtain ⟨c, hbc, _⟩ := hbCopy
  have hr : TreeLeafParent G r := ⟨a, har, ha⟩
  have hc : TreeLeafParent G c := ⟨b, hbc, hb⟩
  have hrnot := leaf_pair_center_not_leaf G r (hpair r hr)
  have hcnot := leaf_pair_center_not_leaf G c (hpair c hc)
  have harne : a ≠ r := har.ne
  have hcbne : c ≠ b := hbc.ne'
  have hacne : a ≠ c := by
    intro heq
    exact hcnot (heq ▸ ha)
  have hrbne : r ≠ b := by
    intro heq
    exact hrnot (heq.symm ▸ hb)
  by_cases hrc : r = c
  · subst c
    let q : G.Walk a b := Walk.cons har (Walk.cons hbc.symm Walk.nil)
    have hq : q.IsPath := by
      simp [q, isPath_def, harne, hab, hbc.ne']
    have heq : p = q := Subtype.mk.inj
      (hG.isAcyclic.subsingleton_path a b |>.elim ⟨p, hp⟩ ⟨q, hq⟩)
    rw [heq] at hz
    have hcases : z = a ∨ z = r ∨ z = b := by simpa [q] using hz
    rcases hcases with rfl | rfl | rfl
    · exact Or.inl ha
    · exact Or.inr hr
    · exact Or.inl hb
  · have hrcAdj := hclique r c hr hc hrc
    let q : G.Walk a b := Walk.cons har (Walk.cons hrcAdj (Walk.cons hbc.symm Walk.nil))
    have hq : q.IsPath := by
      simp [q, isPath_def, harne, hacne, hab, hrc, hrbne, hcbne]
    have heq : p = q := Subtype.mk.inj
      (hG.isAcyclic.subsingleton_path a b |>.elim ⟨p, hp⟩ ⟨q, hq⟩)
    rw [heq] at hz
    have hcases : z = a ∨ z = r ∨ z = c ∨ z = b := by simpa [q] using hz
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl ha
    · exact Or.inr hr
    · exact Or.inr hc
    · exact Or.inl hb

theorem support_cherry_leaf_parent_cover (G : SimpleGraph V) (hG : G.IsTree)
    (hU : EveryMinimumSupport G.Adj) (hcherry : ∃ c, TreeLeafPairCenter G c)
    (z : V) : TreeLeaf G z ∨ TreeLeafParent G z := by
  classical
  have hcherryCopy := hcherry
  obtain ⟨_, a, b, hab, _, _, _, _⟩ := hcherryCopy
  have : Nontrivial V := ⟨⟨a, b, hab⟩⟩
  exact finite_tree_leaf_parent_clique_cover G hG
    (support_cherry_leaf_parent_has_pair G hG.connected hU hcherry)
    (support_cherry_leaf_parents_clique G hG.connected hU hcherry) z

theorem support_cherry_nonleaf_has_pair (G : SimpleGraph V) (hG : G.IsTree)
    (hU : EveryMinimumSupport G.Adj) (hcherry : ∃ c, TreeLeafPairCenter G c)
    (r : V) (hr : ¬ TreeLeaf G r) : TreeLeafPairCenter G r := by
  rcases support_cherry_leaf_parent_cover G hG hU hcherry r with hleaf | hparent
  · exact False.elim (hr hleaf)
  · exact support_cherry_leaf_parent_has_pair G hG.connected hU hcherry r hparent

theorem support_cherry_nonleaf_clique (G : SimpleGraph V) (hG : G.IsTree)
    (hU : EveryMinimumSupport G.Adj) (hcherry : ∃ c, TreeLeafPairCenter G c)
    (r c : V) (hr : ¬ TreeLeaf G r) (hc : ¬ TreeLeaf G c) (hrc : r ≠ c) : G.Adj r c := by
  have hp (x : V) (hx : ¬ TreeLeaf G x) : TreeLeafParent G x := by
    rcases support_cherry_leaf_parent_cover G hG hU hcherry x with hleaf | hparent
    · exact False.elim (hx hleaf)
    · exact hparent
  exact support_cherry_leaf_parents_clique G hG.connected hU hcherry r c (hp r hr) (hp c hc) hrc


end FaultObservationResearch
