module

/-
Longest paths with branch-vertex endpoints in a finite tree.
Standard maximal-path tools for the remaining multiple-branch exhaustion.
These statements do not supply the full pendant-arm decomposition.
-/
public import «formalization-single-branch-realization»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem finite_maximal_branch_path (G : SimpleGraph V) (hG : G.IsTree)
    (hexists : ∃ a b, TreeBranchVertex G a ∧ TreeBranchVertex G b ∧ a ≠ b) :
    ∃ (a b : V) (p : G.Walk a b),
      TreeBranchVertex G a ∧ TreeBranchVertex G b ∧ a ≠ b ∧ p.IsPath ∧
      ∀ (x y : V) (q : G.Walk x y), TreeBranchVertex G x → TreeBranchVertex G y →
        x ≠ y → q.IsPath → q.length ≤ p.length := by
  classical
  let lengths : Set ℕ := {n | ∃ (a b : V) (p : G.Walk a b),
    TreeBranchVertex G a ∧ TreeBranchVertex G b ∧ a ≠ b ∧ p.IsPath ∧ p.length = n}
  have hfinite : lengths.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, _, _, _, hp, hn⟩ => hn ▸ hp.isTrail.length_le_card_edgeFinset
  obtain ⟨x, y, hx, hy, hxy⟩ := hexists
  obtain ⟨q, hq⟩ := hG.exists_isPath x y
  have hnonempty : lengths.Nonempty := ⟨q.length, x, y, q, hx, hy, hxy, hq, rfl⟩
  obtain ⟨_, ⟨⟨a, b, p, ha, hb, hab, hp, _⟩, hmax⟩⟩ := hfinite.exists_maximal hnonempty
  refine ⟨a, b, p, ha, hb, hab, hp, ?_⟩
  intro c d r hc hd hcd hr
  have h := hmax ⟨c, d, r, hc, hd, hcd, hr, rfl⟩
  omega

omit [Fintype V] [DecidableEq V] in
theorem branch_path_start_off_neighbor_nonbranch (G : SimpleGraph V) (a b : V)
    (p : G.Walk a b) (hp : p.IsPath) (hb : TreeBranchVertex G b)
    (hmax : ∀ (x y : V) (q : G.Walk x y), TreeBranchVertex G x → TreeBranchVertex G y →
      x ≠ y → q.IsPath → q.length ≤ p.length)
    (x : V) (hax : G.Adj a x) (hout : x ∉ p.support) : ¬ TreeBranchVertex G x := by
  intro hbranch
  have hxb : x ≠ b := by
    intro heq
    exact hout (heq ▸ p.end_mem_support)
  have hnew : (p.cons hax.symm).IsPath := hp.cons hout
  have h := hmax x b (p.cons hax.symm) hbranch hb hxb hnew
  simp only [length_cons] at h
  omega

omit [Fintype V] [DecidableEq V] in
theorem branch_path_end_off_neighbor_nonbranch (G : SimpleGraph V) (a b : V)
    (p : G.Walk a b) (hp : p.IsPath) (ha : TreeBranchVertex G a)
    (hmax : ∀ (x y : V) (q : G.Walk x y), TreeBranchVertex G x → TreeBranchVertex G y →
      x ≠ y → q.IsPath → q.length ≤ p.length)
    (x : V) (hbx : G.Adj b x) (hout : x ∉ p.support) : ¬ TreeBranchVertex G x := by
  intro hbranch
  have hax : a ≠ x := by
    intro heq
    exact hout (heq ▸ p.start_mem_support)
  have hnew : (p.concat hbx).IsPath := hp.concat hout hbx
  have h := hmax a x (p.concat hbx) ha hbranch hax hnew
  simp only [length_concat] at h
  omega

omit [Fintype V] [DecidableEq V] in
theorem acyclic_paths_same_snd_of_common_vertex (G : SimpleGraph V) (hG : G.IsAcyclic)
    (a b c : V) (p : G.Walk a b) (q : G.Walk a c)
    (hp : p.IsPath) (hq : q.IsPath) (z : V)
    (hzp : z ∈ p.support) (hzq : z ∈ q.support) (hza : z ≠ a) : p.snd = q.snd := by
  classical
  have heq := (hG.subsingleton_path a z).elim
    (⟨p.takeUntil z hzp, hp.takeUntil hzp⟩ : G.Path a z)
    (⟨q.takeUntil z hzq, hq.takeUntil hzq⟩ : G.Path a z)
  have h := congrArg (fun r : G.Path a z => r.val.snd) heq
  simpa only [snd_takeUntil hza] using h

omit [Fintype V] [DecidableEq V] in
theorem tree_off_component_attachment_not_on_path (G : SimpleGraph V) (hG : G.IsAcyclic)
    (a b : V) (hab : a ≠ b) (p : G.Walk a b) (hp : p.IsPath)
    (C : (treeCutGraph G a).ConnectedComponent) (s : C) (hs : G.Adj a s.val.val)
    (hoff : (⟨b, hab.symm⟩ : TreeCutVertex a) ∉ C.supp) : s.val.val ∉ p.support := by
  classical
  intro hmem
  have heq : s.val.val = p.snd := hG.eq_snd_of_adj_start hp hs hmem
  have hnil : ¬ p.Nil := not_nil_of_ne hab
  have hnot : a ∉ p.tail.support := by
    have hnodup := hp.support_nodup
    rw [← p.cons_support_tail hnil] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hinside : ∀ z ∈ p.tail.support, z ∈ {z | z ≠ a} := by
    intro z hz heqa
    exact hnot (heqa ▸ hz)
  let first : TreeCutVertex a := ⟨p.snd, (p.adj_snd hnil).ne'⟩
  have hreach0 : (treeCutGraph G a).Reachable first ⟨b, hab.symm⟩ :=
    (p.tail.induce {z | z ≠ a} hinside).reachable
  have hsfirst : s.val = first := Subtype.ext heq
  have hreach : (treeCutGraph G a).Reachable s.val ⟨b, hab.symm⟩ := by
    rw [hsfirst]
    exact hreach0
  apply hoff
  exact (C.mem_supp_iff _).mpr
    ((ConnectedComponent.sound hreach).symm.trans ((C.mem_supp_iff _).mp s.property))

omit [Fintype V] [DecidableEq V] in
theorem branch_path_off_component_nonbranch (G : SimpleGraph V) (hG : G.IsTree)
    (a b : V) (hab : a ≠ b) (p : G.Walk a b) (hp : p.IsPath) (hb : TreeBranchVertex G b)
    (hmax : ∀ (x y : V) (q : G.Walk x y), TreeBranchVertex G x → TreeBranchVertex G y →
      x ≠ y → q.IsPath → q.length ≤ p.length)
    (C : (treeCutGraph G a).ConnectedComponent)
    (hoff : (⟨b, hab.symm⟩ : TreeCutVertex a) ∉ C.supp) :
    ∀ w : C, ¬ TreeBranchVertex G w.val.val := by
  classical
  obtain ⟨s, hs⟩ := connected_cut_component_has_neighbor G hG.connected a C
  have hout := tree_off_component_attachment_not_on_path G hG.isAcyclic a b hab p hp C s hs hoff
  have hnil : ¬ p.Nil := not_nil_of_ne hab
  have hnot : a ∉ p.tail.support := by
    have hnodup := hp.support_nodup
    rw [← p.cons_support_tail hnil] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  intro w hwbranch
  obtain ⟨q, hq⟩ := (C.reachable_of_mem_supp s.property w.property).exists_isPath
  let f : treeCutGraph G a ↪g G := SimpleGraph.Embedding.induce {z | z ≠ a}
  have hqmap : (q.map f.toHom).IsPath := hq.map f.injective
  have hrootnot : a ∉ (q.map f.toHom).support := by
    rw [SimpleGraph.Walk.support_map]
    intro h
    obtain ⟨z, _, hz⟩ := List.mem_map.mp h
    exact z.property hz
  let r : G.Walk a w.val.val := (q.map f.toHom).cons hs
  have hr : r.IsPath := hqmap.cons hrootnot
  have hdisjoint : r.reverse.support.Disjoint p.support.tail := by
    apply List.disjoint_left.mpr
    intro z hzr hzp
    have hzr0 : z ∈ r.support := by
      simpa only [support_reverse, List.mem_reverse] using hzr
    have hzp0 : z ∈ p.support := List.mem_of_mem_tail hzp
    have hztail : z ∈ p.tail.support := by
      simpa only [p.support_tail_of_not_nil hnil] using hzp
    have hza : z ≠ a := fun heq => hnot (heq ▸ hztail)
    have heq := acyclic_paths_same_snd_of_common_vertex G hG.isAcyclic
      a w.val.val b r p hr hp z hzr0 hzp0 hza
    have hrsnd : r.snd = s.val.val := (q.map f.toHom).snd_cons hs
    have hsnd : s.val.val = p.snd := hrsnd.symm.trans heq
    apply hout
    rw [hsnd]
    exact p.getVert_mem_support 1
  have hpath : (r.reverse.append p).IsPath :=
    (isPath_append r.reverse p).mpr ⟨hr.reverse, hp.tail, hdisjoint⟩
  have hwb : w.val.val ≠ b := by
    intro heq
    have heqsub : w.val = (⟨b, hab.symm⟩ : TreeCutVertex a) := Subtype.ext heq
    apply hoff
    rw [← heqsub]
    exact w.property
  have hlength : r.length = q.length + 1 := by
    change (q.map f.toHom).length + 1 = q.length + 1
    rw [SimpleGraph.Walk.length_map]
  have h := hmax w.val.val b (r.reverse.append p) hwbranch hb hwb hpath
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hlength] at h
  omega

omit [Fintype V] [DecidableEq V] in
theorem branch_path_end_off_component_nonbranch (G : SimpleGraph V) (hG : G.IsTree)
    (a b : V) (hab : a ≠ b) (p : G.Walk a b) (hp : p.IsPath) (ha : TreeBranchVertex G a)
    (hmax : ∀ (x y : V) (q : G.Walk x y), TreeBranchVertex G x → TreeBranchVertex G y →
      x ≠ y → q.IsPath → q.length ≤ p.length)
    (C : (treeCutGraph G b).ConnectedComponent)
    (hoff : (⟨a, hab⟩ : TreeCutVertex b) ∉ C.supp) :
    ∀ w : C, ¬ TreeBranchVertex G w.val.val := by
  apply branch_path_off_component_nonbranch G hG b a hab.symm p.reverse hp.reverse ha
  · intro x y q hx hy hxy hq
    simpa only [length_reverse] using hmax x y q hx hy hxy hq
  · exact hoff

omit [DecidableEq V] in
theorem finite_rooted_nonbranch_cut_component_path (G : SimpleGraph V) (hG : G.IsTree)
    (root : V) (C : (treeCutGraph G root).ConnectedComponent)
    (hnobranch : ∀ x : C, ¬ TreeBranchVertex G x.val.val) :
    ∃ a : C, G.Adj root a.val.val ∧
      ∃ n, 1 ≤ n ∧ ∃ e : C.toSimpleGraph ≃g SimpleGraph.pathGraph n, (e a).val = 0 := by
  classical
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨a, ha⟩ := connected_cut_component_has_neighbor G hG.connected root C
  refine ⟨a, ha, ?_⟩
  apply finite_rooted_nonbranch_tree_path C.toSimpleGraph (tree_cut_component_isTree G hG root C) a
  · intro x hx
    let e : C.toSimpleGraph ↪g G :=
      (SimpleGraph.Embedding.induce {z | z ≠ root}).comp (SimpleGraph.Embedding.induce C.supp)
    exact hnobranch x (branch_vertex_of_embedding C.toSimpleGraph G e x hx)
  · intro x y hx hy
    by_contra hne
    have hxy : x.val.val ≠ y.val.val := by
      intro heq
      exact hne (Subtype.ext (Subtype.ext heq))
    exact hnobranch a ⟨root, x.val.val, y.val.val, ha.symm, hx, hy,
      x.val.property.symm, y.val.property.symm, hxy⟩

omit [DecidableEq V] in
theorem finite_terminal_branch_path_components (G : SimpleGraph V) (hG : G.IsTree)
    (hexists : ∃ a b, TreeBranchVertex G a ∧ TreeBranchVertex G b ∧ a ≠ b) :
    ∃ (a b : V) (hab : a ≠ b) (p : G.Walk a b),
      TreeBranchVertex G a ∧ TreeBranchVertex G b ∧ p.IsPath ∧
      (∀ (x y : V) (q : G.Walk x y), TreeBranchVertex G x → TreeBranchVertex G y →
        x ≠ y → q.IsPath → q.length ≤ p.length) ∧
      (∀ C : (treeCutGraph G a).ConnectedComponent,
        (⟨b, hab.symm⟩ : TreeCutVertex a) ∉ C.supp →
        ∃ s : C, G.Adj a s.val.val ∧ ∃ n, 1 ≤ n ∧
          ∃ e : C.toSimpleGraph ≃g SimpleGraph.pathGraph n, (e s).val = 0) ∧
      (∀ C : (treeCutGraph G b).ConnectedComponent,
        (⟨a, hab⟩ : TreeCutVertex b) ∉ C.supp →
        ∃ s : C, G.Adj b s.val.val ∧ ∃ n, 1 ≤ n ∧
          ∃ e : C.toSimpleGraph ≃g SimpleGraph.pathGraph n, (e s).val = 0) := by
  classical
  obtain ⟨a, b, p, ha, hb, hab, hp, hmax⟩ := finite_maximal_branch_path G hG hexists
  refine ⟨a, b, hab, p, ha, hb, hp, hmax, ?_, ?_⟩
  · intro C hoff
    exact finite_rooted_nonbranch_cut_component_path G hG a C
      (branch_path_off_component_nonbranch G hG a b hab p hp hb hmax C hoff)
  · intro C hoff
    exact finite_rooted_nonbranch_cut_component_path G hG b C
      (branch_path_end_off_component_nonbranch G hG a b hab p hp ha hmax C hoff)

omit [DecidableEq V] in
theorem branch_vertex_cut_components_card (G : SimpleGraph V) (hG : G.IsTree)
    (root : V) (hbranch : TreeBranchVertex G root) :
    3 ≤ Nat.card (treeCutGraph G root).ConnectedComponent := by
  classical
  let : Fintype (treeCutGraph G root).ConnectedComponent := Fintype.ofFinite _
  have hinj : ∀ (x y : V) (hx : G.Adj root x) (hy : G.Adj root y),
      (treeCutGraph G root).connectedComponentMk ⟨x, hx.ne'⟩ =
        (treeCutGraph G root).connectedComponentMk ⟨y, hy.ne'⟩ → x = y := by
    intro x y hx hy heq
    have h := acyclic_cut_neighbors_unique G hG.isAcyclic root
      ⟨x, hx.ne'⟩ ⟨y, hy.ne'⟩ hx hy (ConnectedComponent.exact heq)
    exact congrArg Subtype.val h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := hbranch
  let Cx := (treeCutGraph G root).connectedComponentMk ⟨x, hx.ne'⟩
  let Cy := (treeCutGraph G root).connectedComponentMk ⟨y, hy.ne'⟩
  let Cz := (treeCutGraph G root).connectedComponentMk ⟨z, hz.ne'⟩
  have hXY : Cx ≠ Cy := fun h => hxy (hinj x y hx hy h)
  have hXZ : Cx ≠ Cz := fun h => hxz (hinj x z hx hz h)
  have hYZ : Cy ≠ Cz := fun h => hyz (hinj y z hy hz h)
  have hthree : ({Cx, Cy, Cz} : Finset (treeCutGraph G root).ConnectedComponent).card = 3 := by
    simp [hXY, hXZ, hYZ]
  have hupper := Finset.card_le_univ ({Cx, Cy, Cz} : Finset (treeCutGraph G root).ConnectedComponent)
  simpa only [hthree, Finset.card_univ, Nat.card_eq_fintype_card] using hupper

omit [DecidableEq V] in
theorem branch_vertex_two_off_components (G : SimpleGraph V) (hG : G.IsTree)
    (a b : V) (hab : a ≠ b) (ha : TreeBranchVertex G a) :
    ∃ C D : (treeCutGraph G a).ConnectedComponent,
      C ≠ D ∧ (⟨b, hab.symm⟩ : TreeCutVertex a) ∉ C.supp ∧
        (⟨b, hab.symm⟩ : TreeCutVertex a) ∉ D.supp := by
  classical
  let : Fintype (treeCutGraph G a).ConnectedComponent := Fintype.ofFinite _
  let main := (treeCutGraph G a).connectedComponentMk ⟨b, hab.symm⟩
  have hcard : 3 ≤ Fintype.card (treeCutGraph G a).ConnectedComponent := by
    simpa only [Nat.card_eq_fintype_card] using branch_vertex_cut_components_card G hG a ha
  have hfirst : ({main} : Finset (treeCutGraph G a).ConnectedComponent).card <
      (Finset.univ : Finset (treeCutGraph G a).ConnectedComponent).card := by
    simp only [Finset.card_singleton, Finset.card_univ]
    omega
  obtain ⟨C, _, hC⟩ := Finset.exists_mem_notMem_of_card_lt_card hfirst
  have hCne : C ≠ main := by simpa only [Finset.mem_singleton] using hC
  have hpair : ({main, C} : Finset (treeCutGraph G a).ConnectedComponent).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr hCne.symm
  have hsecond : ({main, C} : Finset (treeCutGraph G a).ConnectedComponent).card <
      (Finset.univ : Finset (treeCutGraph G a).ConnectedComponent).card := by
    rw [hpair, Finset.card_univ]
    omega
  obtain ⟨D, _, hD⟩ := Finset.exists_mem_notMem_of_card_lt_card hsecond
  have hDne : D ≠ main ∧ D ≠ C := by simpa using hD
  refine ⟨C, D, hDne.2.symm, ?_, ?_⟩
  · intro hb
    exact hCne ((C.mem_supp_iff _).mp hb).symm
  · intro hb
    exact hDne.1 ((D.mem_supp_iff _).mp hb).symm

end FaultObservationResearch
