module

/-
Standard rooted path decomposition for pending branch-component extraction.
Draft until compiled and axiom-audited. It does not prove the remaining
one-branch or multiple-branch cases of the time-support classification.
-/
public import «formalization-tree-nonbranch-path»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem finite_maximal_path_from_vertex (G : SimpleGraph V) (root : V) :
    ∃ (b : V) (p : G.Walk root b), p.IsPath ∧
      ∀ (b' : V) (q : G.Walk root b'), q.IsPath → q.length ≤ p.length := by
  classical
  let s : Set ℕ := {n | ∃ (b : V) (p : G.Walk root b), p.IsPath ∧ p.length = n}
  have hfinite : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, hp, hn⟩ => hn ▸ hp.isTrail.length_le_card_edgeFinset
  obtain ⟨_, ⟨⟨b, p, hp, hpn⟩, hmax⟩⟩ :=
    hfinite.exists_maximal ⟨0, ⟨root, Walk.nil, by simp, rfl⟩⟩
  refine ⟨b, p, hp, ?_⟩
  intro b' q hq
  have h := hmax ⟨b', q, hq, rfl⟩
  omega

omit [Fintype V] [DecidableEq V] in
theorem rooted_nonbranch_maximal_path_neighbor_closed (G : SimpleGraph V)
    (hnobranch : ∀ x, ¬ TreeBranchVertex G x)
    (root b : V) (hroot : ∀ x y, G.Adj root x → G.Adj root y → x = y)
    (p : G.Walk root b) (hp : p.IsPath)
    (hmax : ∀ (b' : V) (q : G.Walk root b'), q.IsPath → q.length ≤ p.length) :
    ∀ x ∈ p.support, ∀ y, G.Adj x y → y ∈ p.support := by
  classical
  intro x hx y hxy
  by_contra hy
  by_cases hxr : x = root
  · subst x
    by_cases hnil : p.Nil
    · have hzero := length_eq_zero_iff.mpr hnil
      have h := hmax y hxy.toWalk (IsPath.of_adj hxy)
      change 1 ≤ p.length at h
      omega
    · have hys : y = p.snd := hroot y p.snd hxy (p.adj_snd hnil)
      exact hy (hys.symm ▸ p.getVert_mem_support 1)
  by_cases hxb : x = b
  · subst x
    have hnew : (p.concat hxy).IsPath := hp.concat hy hxy
    have h := hmax y (p.concat hxy) hnew
    simp only [length_concat] at h
    omega
  obtain ⟨i, hix, hi⟩ := mem_support_iff_exists_getVert.mp hx
  have hi0 : 0 < i := by
    by_contra h
    have hiZero : i = 0 := by omega
    exact hxr (hix.symm.trans (by simp [hiZero]))
  have hiLast : i < p.length := by
    by_contra h
    have hiEnd : i = p.length := by omega
    exact hxb (hix.symm.trans (by simp [hiEnd]))
  have hleft : G.Adj x (p.getVert (i - 1)) := by
    have h := (p.adj_getVert_succ (i := i - 1) (by omega)).symm
    have heq : i - 1 + 1 = i := by omega
    simpa only [heq, hix] using h
  have hright : G.Adj x (p.getVert (i + 1)) := by
    simpa only [hix] using p.adj_getVert_succ hiLast
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have h := hp.getVert_injOn (by rw [Set.mem_ofPred_eq]; omega)
      (by rw [Set.mem_ofPred_eq]; omega) heq
    omega
  have hleftNe : p.getVert (i - 1) ≠ y := by
    intro heq
    exact hy (heq ▸ p.getVert_mem_support (i - 1))
  have hrightNe : p.getVert (i + 1) ≠ y := by
    intro heq
    exact hy (heq ▸ p.getVert_mem_support (i + 1))
  exact hnobranch x ⟨p.getVert (i - 1), p.getVert (i + 1), y,
    hleft, hright, hxy, hne, hleftNe, hrightNe⟩

omit [Fintype V] [DecidableEq V] in
theorem tree_spanning_path_iso_start (G : SimpleGraph V) (hG : G.IsTree)
    (a b : V) (p : G.Walk a b) (hp : p.IsPath)
    (hcover : ∀ x, x ∈ p.support) :
    ∃ e : G ≃g SimpleGraph.pathGraph (p.length + 1), e a = 0 := by
  classical
  have hspan : p.toSubgraph.IsSpanning := by
    intro x
    exact p.mem_verts_toSubgraph.mpr (hcover x)
  let eSpan := p.toSubgraph.spanningCoeEquivCoeOfSpanning hspan
  have hconn : p.toSubgraph.spanningCoe.Connected :=
    eSpan.connected_iff.mpr p.toSubgraph_connected.coe
  have hle : G ≤ p.toSubgraph.spanningCoe :=
    (SimpleGraph.isTree_iff_minimal_connected.mp hG).2 hconn p.toSubgraph.spanningCoe_le
  have heq : p.toSubgraph.spanningCoe = G :=
    le_antisymm p.toSubgraph.spanningCoe_le hle
  let eIdentity : p.toSubgraph.spanningCoe ≃g G := {
    toEquiv := Equiv.refl V
    map_rel_iff' := by
      intro x y
      change G.Adj x y ↔ p.toSubgraph.spanningCoe.Adj x y
      rw [heq] }
  let e := (hp.pathGraphIsoToSubgraph.trans eSpan.symm).trans eIdentity
  have hstart : e 0 = a := by
    change p.support[0] = a
    simp [support_getElem_eq_getVert]
  refine ⟨e.symm, ?_⟩
  apply e.injective
  simpa using hstart.symm

omit [DecidableEq V] in
theorem finite_rooted_nonbranch_tree_path (G : SimpleGraph V) (hG : G.IsTree)
    (root : V) (hnobranch : ∀ x, ¬ TreeBranchVertex G x)
    (hroot : ∀ x y, G.Adj root x → G.Adj root y → x = y) :
    ∃ n, 1 ≤ n ∧ ∃ e : G ≃g SimpleGraph.pathGraph n, (e root).val = 0 := by
  classical
  obtain ⟨b, p, hp, hmax⟩ := finite_maximal_path_from_vertex G root
  have hclosed := rooted_nonbranch_maximal_path_neighbor_closed G hnobranch root b hroot p hp hmax
  have hset : {x | x ∈ p.support} = Set.univ :=
    connected_neighbor_closed_eq_univ G hG.connected {x | x ∈ p.support} root p.start_mem_support hclosed
  have hcover : ∀ x, x ∈ p.support := by
    intro x
    change x ∈ {x | x ∈ p.support}
    rw [hset]
    exact Set.mem_univ x
  obtain ⟨e, he⟩ := tree_spanning_path_iso_start G hG root b p hp hcover
  exact ⟨p.length + 1, by omega, e, congrArg Fin.val he⟩

end FaultObservationResearch
