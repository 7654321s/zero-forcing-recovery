module

/- Close the adjacent terminal-pair case by reducing its residual core to an edge. -/
public import «formalization-tree-terminal-exhaustion»
public import «formalization-adjacent-equal»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
open SimpleGraph SimpleGraph.Walk
universe u
variable {V : Type u}

theorem connected_two_neighbor_core_cover (G : SimpleGraph V) (hG : G.Connected)
    (a b : V) (ha : ∀ z, G.Adj a z → z = b) (hb : ∀ z, G.Adj b z → z = a) :
    ∀ z, z = a ∨ z = b := by
  have hw : ∀ (x y : V) (p : G.Walk x y), x = a ∨ x = b → y = a ∨ y = b := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z h p ih =>
      intro hx
      apply ih
      rcases hx with rfl | rfl
      · exact Or.inr (ha y h)
      · exact Or.inl (hb y h)
  intro z
  exact hw a z (hG a z).some (Or.inl rfl)

def twoPointCoreMap (a b : V) (i : Fin 2) : V := if i = 0 then a else b

theorem twoPointCoreMap_bijective (a b : V) (hab : a ≠ b)
    (hcover : ∀ z, z = a ∨ z = b) : Function.Bijective (twoPointCoreMap a b) := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [twoPointCoreMap]
  · intro z
    rcases hcover z with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

def twoPointCoreIso (G : SimpleGraph V) (a b : V) (hab : a ≠ b) (hadj : G.Adj a b)
    (hcover : ∀ z, z = a ∨ z = b) : SimpleGraph.pathGraph 2 ≃g G where
  toEquiv := Equiv.ofBijective (twoPointCoreMap a b) (twoPointCoreMap_bijective a b hab hcover)
  map_rel_iff' := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [twoPointCoreMap, SimpleGraph.pathGraph_adj, hadj, hadj.symm]

theorem sorted_adjacent_canonical_realization [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (a b : V) (hab : a ≠ b) (A : SortedTerminalArms G a b hab)
    (B : SortedTerminalArms G b a hab.symm) (haextra : A.extra = 0) (hbextra : B.extra = 0)
    (hadj : G.Adj a b) :
    ∃ (m n k l : ℕ), Nonempty (twoCenterGraph (SimpleGraph.pathGraph 2) (0 : Fin 2) 1 m n k l ≃g G) ∧
      m + 1 = Nat.card (sortedLongestPair G b a hab.symm B).first ∧
      n + 1 = Nat.card (sortedLongestPair G b a hab.symm B).second ∧
      k + 1 = Nat.card (sortedLongestPair G a b hab A).first ∧
      l + 1 = Nat.card (sortedLongestPair G a b hab A).second := by
  classical
  let P := sortedLongestPair G a b hab A
  let Q := sortedLongestPair G b a hab.symm B
  let S₁ := treeComponentRemainderSet G a ({P.first, P.second} : Set _)
  let R₁ := treeComponentRemainderGraph G a {P.first, P.second}
  let a₁ : S₁ := twoComponentCoreRoot G a P.first P.second
  have hR₁ : R₁.IsTree := tree_component_remainder_isTree G hG a {P.first, P.second}
  obtain ⟨hb, Q₁, hc₁, hc₂, hm₁, hm₂⟩ := terminal_pair_opposite_path_components G hG.connected a b hab P Q
  let b₁ : S₁ := ⟨b, hb⟩
  have hba : b₁ ≠ a₁ := fun h => hab.symm (congrArg Subtype.val h)
  let S₂ := treeComponentRemainderSet R₁ b₁ ({Q₁.first, Q₁.second} : Set _)
  let R₂ := treeComponentRemainderGraph R₁ b₁ {Q₁.first, Q₁.second}
  have hR₂ : R₂.IsTree := tree_component_remainder_isTree R₁ hR₁ b₁ {Q₁.first, Q₁.second}
  have ha : a₁ ∈ S₂ := by
    apply tree_off_components_keep_other_vertex R₁ b₁ a₁ hba.symm {Q₁.first, Q₁.second}
    intro C hC
    have hc : C = Q₁.first ∨ C = Q₁.second := by simpa using hC
    rcases hc with rfl | rfl
    · exact Q₁.first_off
    · exact Q₁.second_off
  let a₂ : S₂ := ⟨a₁, ha⟩
  let b₂ : S₂ := twoComponentCoreRoot R₁ b₁ Q₁.first Q₁.second
  have hba₂ : b₂ ≠ a₂ := fun h => hba (congrArg Subtype.val h)
  have hab₂ : R₂.Adj b₂ a₂ := hadj.symm
  have hNa : ∀ z, R₂.Adj a₂ z → z = b₂ := by
    intro z hz
    apply Subtype.ext
    apply Subtype.ext
    exact sorted_terminal_adjacent_core_root_neighbor G hG a b hab A haextra hadj z.val hz
  have hNb : ∀ z, R₂.Adj b₂ z → z = a₂ := by
    intro z hz
    by_contra hne
    have hza : z.val.val ≠ a := by
      intro heq
      exact hne (Subtype.ext (Subtype.ext heq))
    have hzb : z.val.val ≠ b := by
      intro heq
      exact hz.ne' (Subtype.ext (Subtype.ext heq))
    let zcut : TreeCutVertex b := ⟨z.val.val, hzb⟩
    let C := (treeCutGraph G b).connectedComponentMk zcut
    have hzC : zcut ∈ C.supp := (C.mem_supp_iff zcut).mpr rfl
    have hoff : (⟨a, hab⟩ : TreeCutVertex b) ∉ C.supp := by
      intro haC
      have heq := acyclic_cut_neighbors_unique G hG.isAcyclic b zcut ⟨a, hab⟩
        hz hadj.symm (C.reachable_of_mem_supp hzC haC)
      exact hza (congrArg Subtype.val heq)
    have hchoice := sorted_terminal_off_components_exhausted G b a hab.symm B hbextra C hoff
    let zcut₁ : TreeCutVertex b₁ := ⟨z.val, fun h => hzb (congrArg Subtype.val h)⟩
    apply z.property (fun h => hzb (congrArg Subtype.val h))
    change (treeCutGraph R₁ b₁).connectedComponentMk zcut₁ ∈ ({Q₁.first, Q₁.second} : Set _)
    rcases hchoice with hfirst | hsecond
    · have hmem : cutInducedForgetHom G S₁ b hb zcut₁ ∈ Q.first.supp := by
        change zcut ∈ Q.first.supp
        rw [← hfirst]
        exact hzC
      have hmk := (Q₁.first.mem_supp_iff _).mp ((hm₁ zcut₁).mpr hmem)
      exact Or.inl hmk
    · have hmem : cutInducedForgetHom G S₁ b hb zcut₁ ∈ Q.second.supp := by
        change zcut ∈ Q.second.supp
        rw [← hsecond]
        exact hzC
      have hmk := (Q₁.second.mem_supp_iff _).mp ((hm₂ zcut₁).mpr hmem)
      exact Or.inr hmk
  let ecore := twoPointCoreIso R₂ b₂ a₂ hba₂ hab₂
    (connected_two_neighbor_core_cover R₂ hR₂.connected b₂ a₂ hNb hNa)
  obtain ⟨s, k, hs, e, he⟩ := P.first_path
  obtain ⟨t, l, ht, f, hf⟩ := P.second_path
  let e₁ : twoPendantGraph R₁ a₁ k l ≃g G :=
    twoCutPathsRealizationIso G hG a P.first P.second P.distinct k l s hs t ht e f he hf
  obtain ⟨s', m, hs', e', he'⟩ := Q₁.first_path
  obtain ⟨t', n, ht', f', hf'⟩ := Q₁.second_path
  let e₂ : twoPendantGraph R₂ b₂ m n ≃g R₁ :=
    twoCutPathsRealizationIso R₁ hR₁ b₁ Q₁.first Q₁.second Q₁.distinct m n
      s' hs' t' ht' e' f' he' hf'
  let e₃ := twoPendantCongrIso (twoPendantGraph R₂ b₂ m n) R₁ e₂
    (twoPendantCore S₂ m n a₂) a₁ rfl k l
  let e₄ := twoPendantCongrIso (SimpleGraph.pathGraph 2) R₂ ecore 0 b₂ rfl m n
  let e₅ := twoPendantCongrIso (twoPendantGraph (SimpleGraph.pathGraph 2) 0 m n)
    (twoPendantGraph R₂ b₂ m n) e₄ (twoPendantCore (Fin 2) m n 1)
    (twoPendantCore S₂ m n a₂) rfl k l
  refine ⟨m, n, k, l, ⟨e₅.trans (e₃.trans e₁)⟩, ?_, ?_, ?_, ?_⟩
  · have h : Nat.card Q₁.first = m + 1 := by simpa only [Nat.card_fin] using Nat.card_congr e'.toEquiv
    change m + 1 = Nat.card Q.first
    omega
  · have h : Nat.card Q₁.second = n + 1 := by simpa only [Nat.card_fin] using Nat.card_congr f'.toEquiv
    change n + 1 = Nat.card Q.second
    omega
  · have h : Nat.card P.first = k + 1 := by simpa only [Nat.card_fin] using Nat.card_congr e.toEquiv
    exact h.symm
  · have h : Nat.card P.second = l + 1 := by simpa only [Nat.card_fin] using Nat.card_congr f.toEquiv
    exact h.symm

end FaultObservationResearch
