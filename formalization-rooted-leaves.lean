module

/-
Root-inactive leaf forcing, a structural tool for the full tree proof.
The root has no outgoing forces; other vertices keep all original neighbors.
These tools are not claimed as original research results.
-/
public import «formalization-foundations»
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

universe u

def TreeLeaf {V : Type u} (G : SimpleGraph V) (x : V) : Prop :=
  ∃! y : V, G.Adj x y

def RootClosed {V : Type u} (G : SimpleGraph V) (root : V) (blue : Finset V) : Prop :=
  ∀ source ∈ blue, source ≠ root → ∀ target, G.Adj source target →
    (∀ other, G.Adj source other → other ∉ blue → other = target) → target ∈ blue

def rootInactiveAdj {V : Type u} (G : SimpleGraph V) (root source target : V) : Prop :=
  source ≠ root ∧ G.Adj source target

theorem tree_exists_leaf_ne {V : Type u} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) (htree : G.IsTree) (root : V) :
    ∃ leaf : V, TreeLeaf G leaf ∧ leaf ≠ root := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ := htree.exists_ne_and_degree_eq_one
  by_cases har : a = root
  · refine ⟨b, SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hb, ?_⟩
    intro hbr
    exact hab (har.trans hbr.symm)
  · exact ⟨a, SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp ha, har⟩

theorem rootClosed_all_of_leaves {V : Type u} [Fintype V]
    (G : SimpleGraph V) (htree : G.IsTree) (root : V) (blue : Finset V)
    (hblue : blue.Nonempty)
    (hleaves : ∀ x : V, TreeLeaf G x → x ≠ root → x ∈ blue)
    (hclosed : RootClosed G root blue) : blue = Finset.univ := by
  classical
  have general : ∀ n : ℕ, ∀ (U : Type u) [Fintype U] (H : SimpleGraph U),
      Fintype.card U = n → ∀ (r : U) (C : Finset U), H.IsTree → C.Nonempty →
        (∀ x : U, TreeLeaf H x → x ≠ r → x ∈ C) → RootClosed H r C → C = Finset.univ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ H hcard r C hT hC hL hcl
      by_cases hsmall : Subsingleton U
      · obtain ⟨x, hx⟩ := hC
        apply Finset.eq_univ_of_forall
        intro y
        simpa only [hsmall.elim y x] using hx
      · have : Nontrivial U := not_subsingleton_iff_nontrivial.mp hsmall
        obtain ⟨leaf, hLeaf, hLeafRoot⟩ := tree_exists_leaf_ne H hT r
        have hLeafBlue : leaf ∈ C := hL leaf hLeaf hLeafRoot
        obtain ⟨parent, hAdjParent, hUnique⟩ := hLeaf
        have hParentBlue : parent ∈ C :=
          hcl leaf hLeafBlue hLeafRoot parent hAdjParent (fun other ha _ => hUnique other ha)
        have hParentNe : parent ≠ leaf := by
          intro heq
          subst parent
          exact H.loopless.irrefl leaf hAdjParent
        have hDegree : H.degree leaf = 1 :=
          SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨parent, hAdjParent, hUnique⟩
        let S : Set U := {leaf}ᶜ
        let smallGraph : SimpleGraph S := H.induce S
        let rootSub : S := ⟨r, by simp [S, Ne.symm hLeafRoot]⟩
        let smallBlue : Finset S := Finset.univ.filter (fun x => x.val ∈ C)
        have hTreeSmall : smallGraph.IsTree := {
          connected := by
            simpa only [smallGraph, S] using
              hT.connected.induce_compl_singleton_of_degree_eq_one hDegree
          isAcyclic := hT.isAcyclic.induce S }
        have hSmallNonempty : smallBlue.Nonempty := by
          let p : S := ⟨parent, by simp [S, hParentNe]⟩
          exact ⟨p, by simp [smallBlue, p, hParentBlue]⟩
        have hSmallLeaves : ∀ x : S, TreeLeaf smallGraph x → x ≠ rootSub → x ∈ smallBlue := by
          intro x hxLeaf hxRoot
          have hxC : x.val ∈ C := by
            by_cases hAdjLeaf : H.Adj leaf x.val
            · have heq := hUnique x.val hAdjLeaf
              simpa only [heq] using hParentBlue
            · apply hL x.val
              · obtain ⟨q, hq, hqUnique⟩ := hxLeaf
                refine ⟨q.val, hq, ?_⟩
                intro y hy
                have hyNe : y ≠ leaf := by
                  intro heq
                  subst y
                  exact hAdjLeaf (H.symm.symm _ _ hy)
                let ySub : S := ⟨y, by simp [S, hyNe]⟩
                have heq : ySub = q := hqUnique ySub hy
                exact congrArg Subtype.val heq
              · intro heq
                exact hxRoot (Subtype.ext heq)
          simpa only [smallBlue, Finset.mem_filter, Finset.mem_univ, true_and] using hxC
        have hSmallClosed : RootClosed smallGraph rootSub smallBlue := by
          intro source hs hsRoot target ha hu
          have hsC : source.val ∈ C := by simpa [smallBlue] using hs
          have hsNe : source.val ≠ r := by
            intro heq
            exact hsRoot (Subtype.ext heq)
          have htC : target.val ∈ C := by
            apply hcl source.val hsC hsNe target.val ha
            intro other hao hwhite
            have hoNe : other ≠ leaf := by
              intro heq
              exact hwhite (by simpa only [heq] using hLeafBlue)
            let otherSub : S := ⟨other, by simp [S, hoNe]⟩
            have hoWhite : otherSub ∉ smallBlue := by simpa [smallBlue, otherSub] using hwhite
            have heq : otherSub = target := hu otherSub hao hoWhite
            exact congrArg Subtype.val heq
          simpa only [smallBlue, Finset.mem_filter, Finset.mem_univ, true_and] using htC
        have hlt : Fintype.card S < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := leaf) (by simp [S])
        have hFullSmall := ih (Fintype.card S) hlt S smallGraph rfl rootSub smallBlue
          hTreeSmall hSmallNonempty hSmallLeaves hSmallClosed
        apply Finset.eq_univ_of_forall
        intro x
        by_cases hx : x = leaf
        · simpa only [hx] using hLeafBlue
        · let xSub : S := ⟨x, by simp [S, hx]⟩
          have hm : xSub ∈ smallBlue := by rw [hFullSmall]; exact Finset.mem_univ _
          simpa [smallBlue, xSub] using hm
  exact general (Fintype.card V) V G rfl root blue htree hblue hleaves hclosed

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem colorAfter_eq_from_plateau (adj : V → V → Prop) (blue : Finset V)
    (s : ℕ) (hfixed : colorAfter adj blue (s + 1) = colorAfter adj blue s)
    (t : ℕ) (hst : s ≤ t) : colorAfter adj blue t = colorAfter adj blue s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [colorAfter_add, colorAfter_of_fixed adj (colorAfter adj blue s) hfixed]

theorem colorAfter_stabilizes_card (adj : V → V → Prop) (blue : Finset V) :
    colorAfter adj blue (Fintype.card V + 1) = colorAfter adj blue (Fintype.card V) := by
  classical
  by_contra hnot
  let n := Fintype.card V
  have hstrict : ∀ t : ℕ, t ≤ n →
      (colorAfter adj blue t).card < (colorAfter adj blue (t + 1)).card := by
    intro t htn
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨colorAfter_subset_succ adj blue t, ?_⟩
    intro heq
    have hn := colorAfter_eq_from_plateau adj blue t heq.symm n htn
    have hn1 := colorAfter_eq_from_plateau adj blue t heq.symm (n + 1)
      (Nat.le_trans htn (Nat.le_succ n))
    exact hnot (hn1.trans hn.symm)
  have hlower : ∀ t : ℕ, t ≤ n + 1 → t ≤ (colorAfter adj blue t).card := by
    intro t
    induction t with
    | zero => intro _; exact Nat.zero_le _
    | succ t ih =>
      intro ht
      have htn : t ≤ n := Nat.le_of_succ_le_succ ht
      exact Nat.succ_le_of_lt (lt_of_le_of_lt
        (ih (Nat.le_trans htn (Nat.le_succ n))) (hstrict t htn))
  have hupper : (colorAfter adj blue (n + 1)).card ≤ n := by
    simpa only [Finset.card_univ] using
      (Finset.card_le_card (Finset.subset_univ (colorAfter adj blue (n + 1))))
  exact Nat.not_succ_le_self n (Nat.le_trans (hlower (n + 1) le_rfl) hupper)

theorem rootClosed_of_stable (G : SimpleGraph V) (root : V) (blue : Finset V) (t : ℕ)
    (hfixed : colorAfter (rootInactiveAdj G root) blue (t + 1) =
      colorAfter (rootInactiveAdj G root) blue t) :
    RootClosed G root (colorAfter (rootInactiveAdj G root) blue t) := by
  intro source hs hsRoot target ha hu
  have hm : target ∈ synchronousStep (rootInactiveAdj G root)
      (colorAfter (rootInactiveAdj G root) blue t) := by
    apply (mem_synchronousStep _ _ _).mpr
    exact Or.inr ⟨source, hs, ⟨hsRoot, ha⟩,
      fun other hao hwhite => hu other hao.2 hwhite⟩
  change synchronousStep (rootInactiveAdj G root)
    (colorAfter (rootInactiveAdj G root) blue t) =
      colorAfter (rootInactiveAdj G root) blue t at hfixed
  rwa [hfixed] at hm

theorem rooted_leaves_finish_card [Nontrivial V] (G : SimpleGraph V) (htree : G.IsTree)
    (root : V) (blue : Finset V)
    (hleaves : ∀ x : V, TreeLeaf G x → x ≠ root → x ∈ blue) :
    FinishesBy (rootInactiveAdj G root) blue (Fintype.card V) := by
  classical
  let n := Fintype.card V
  let C := colorAfter (rootInactiveAdj G root) blue n
  have hmono : blue ⊆ C := colorAfter_mono_time (rootInactiveAdj G root) blue (Nat.zero_le n)
  obtain ⟨leaf, hLeaf, hLeafRoot⟩ := tree_exists_leaf_ne G htree root
  have hC : C.Nonempty := ⟨leaf, hmono (hleaves leaf hLeaf hLeafRoot)⟩
  have hL : ∀ x : V, TreeLeaf G x → x ≠ root → x ∈ C :=
    fun x hx hr => hmono (hleaves x hx hr)
  have hClosed : RootClosed G root C := rootClosed_of_stable G root blue n
    (colorAfter_stabilizes_card (rootInactiveAdj G root) blue)
  exact rootClosed_all_of_leaves G htree root C hC hL hClosed

theorem rooted_leaves_forcing [Nontrivial V] (G : SimpleGraph V) (htree : G.IsTree)
    (root : V) (blue : Finset V)
    (hleaves : ∀ x : V, TreeLeaf G x → x ≠ root → x ∈ blue) :
    IsForcing (rootInactiveAdj G root) blue :=
  ⟨Fintype.card V, rooted_leaves_finish_card G htree root blue hleaves⟩

end FaultObservationResearch
