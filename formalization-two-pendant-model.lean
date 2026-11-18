module

/-
Two nonempty pendant paths attached to a core. Static forcing tools only;
no sharp propagation-time identity or full tree classification is claimed.
-/
public import «formalization-colored-exterior-embedding»
public import «formalization-path-forcing»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u

abbrev TwoPendantVertex (V : Type u) (a b : ℕ) :=
  V ⊕ (Fin (a + 1) ⊕ Fin (b + 1))

def twoPendantCore (V : Type u) (a b : ℕ) : V ↪ TwoPendantVertex V a b where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def twoPendantA (V : Type u) (a b : ℕ) : Fin (a + 1) ↪ TwoPendantVertex V a b where
  toFun := fun i => Sum.inr (Sum.inl i)
  inj' := by intro i j h; exact Sum.inl_injective (Sum.inr_injective h)

def twoPendantB (V : Type u) (a b : ℕ) : Fin (b + 1) ↪ TwoPendantVertex V a b where
  toFun := fun i => Sum.inr (Sum.inr i)
  inj' := by intro i j h; exact Sum.inr_injective (Sum.inr_injective h)

def twoPendantAdj {V : Type u} (R : SimpleGraph V) (root : V) (a b : ℕ) :
    TwoPendantVertex V a b → TwoPendantVertex V a b → Prop
  | Sum.inl x, Sum.inl y => R.Adj x y
  | Sum.inl x, Sum.inr (Sum.inl i) => x = root ∧ i = 0
  | Sum.inr (Sum.inl i), Sum.inl x => x = root ∧ i = 0
  | Sum.inl x, Sum.inr (Sum.inr j) => x = root ∧ j = 0
  | Sum.inr (Sum.inr j), Sum.inl x => x = root ∧ j = 0
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) =>
      (SimpleGraph.pathGraph (a + 1)).Adj i j
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) =>
      (SimpleGraph.pathGraph (b + 1)).Adj i j
  | _, _ => False

def twoPendantGraph {V : Type u} (R : SimpleGraph V) (root : V) (a b : ℕ) :
    SimpleGraph (TwoPendantVertex V a b) where
  Adj := twoPendantAdj R root a b
  symm := by
    constructor
    rintro (x | (i | j)) (y | (k | l)) h
    · exact R.symm.symm x y h
    · exact h
    · exact h
    · exact h
    · exact (SimpleGraph.pathGraph (a + 1)).symm.symm i k h
    · exact h.elim
    · exact h
    · exact h.elim
    · exact (SimpleGraph.pathGraph (b + 1)).symm.symm j l h
  loopless := by
    constructor
    rintro (x | (i | j)) h
    · exact R.loopless.irrefl x h
    · exact (SimpleGraph.pathGraph (a + 1)).loopless.irrefl i h
    · exact (SimpleGraph.pathGraph (b + 1)).loopless.irrefl j h

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem twoPendant_armA_colors (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hr : twoPendantCore V a b root ∈ C) (hh : twoPendantA V a b 0 ∈ C) :
    ∀ i, twoPendantA V a b i ∈
      colorAfter (twoPendantGraph R root a b).Adj C (a + 1) := by
  classical
  suffices h : ∀ i, twoPendantA V a b i ∈
      colorAfter (twoPendantGraph R root a b).Adj C (Fintype.card (Fin (a + 1))) by
    simpa only [Fintype.card_fin] using h
  apply forcing_embedding_with_blue_exterior_colors_image
    (SimpleGraph.pathGraph (a + 1)) (twoPendantGraph R root a b)
    (twoPendantA V a b) (fun h => h) ({0} : Finset (Fin (a + 1))) C
  · intro i z hz
    rcases z with x | (j | k)
    · change x = root ∧ i = 0 at hz
      rcases hz with ⟨rfl, _⟩
      exact Or.inr hr
    · exact Or.inl ⟨j, rfl, hz⟩
    · exact hz.elim
  · intro i hi
    have hi0 : i = 0 := Finset.mem_singleton.mp hi
    simpa [hi0] using hh
  · exact path_forcing_of_seed a {0} (Or.inl (Finset.mem_singleton_self _))

theorem twoPendant_armB_colors (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hr : twoPendantCore V a b root ∈ C) (hh : twoPendantB V a b 0 ∈ C) :
    ∀ i, twoPendantB V a b i ∈
      colorAfter (twoPendantGraph R root a b).Adj C (b + 1) := by
  classical
  suffices h : ∀ i, twoPendantB V a b i ∈
      colorAfter (twoPendantGraph R root a b).Adj C (Fintype.card (Fin (b + 1))) by
    simpa only [Fintype.card_fin] using h
  apply forcing_embedding_with_blue_exterior_colors_image
    (SimpleGraph.pathGraph (b + 1)) (twoPendantGraph R root a b)
    (twoPendantB V a b) (fun h => h) ({0} : Finset (Fin (b + 1))) C
  · intro i z hz
    rcases z with x | (j | k)
    · change x = root ∧ i = 0 at hz
      rcases hz with ⟨rfl, _⟩
      exact Or.inr hr
    · exact hz.elim
    · exact Or.inl ⟨k, rfl, hz⟩
  · intro i hi
    have hi0 : i = 0 := Finset.mem_singleton.mp hi
    simpa [hi0] using hh
  · exact path_forcing_of_seed b {0} (Or.inl (Finset.mem_singleton_self _))

theorem twoPendant_core_colors_active [Nontrivial V]
    (R : SimpleGraph V) (htree : R.IsTree) (root missing : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hA : twoPendantA V a b 0 ∈ C) (hB : twoPendantB V a b 0 ∈ C)
    (hleaves : ∀ x, TreeLeaf R x → x ≠ missing → twoPendantCore V a b x ∈ C) :
    ∀ x, twoPendantCore V a b x ∈
      colorAfter (twoPendantGraph R root a b).Adj C (Fintype.card V) := by
  classical
  let L := Finset.univ.filter (fun x => TreeLeaf R x ∧ x ≠ missing)
  apply forcing_embedding_with_blue_exterior_colors_image R
    (twoPendantGraph R root a b) (twoPendantCore V a b) (fun h => h) L C
  · intro x z hz
    rcases z with y | (i | j)
    · exact Or.inl ⟨y, rfl, hz⟩
    · change x = root ∧ i = 0 at hz
      exact Or.inr (hz.2 ▸ hA)
    · change x = root ∧ j = 0 at hz
      exact Or.inr (hz.2 ▸ hB)
  · intro x hx
    have hx' : TreeLeaf R x ∧ x ≠ missing := (Finset.mem_filter.mp hx).2
    exact hleaves x hx'.1 hx'.2
  · apply rooted_leaves_forcing_ordinary R htree missing L
    intro x hx hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hm⟩

theorem twoPendant_core_colors_inactive [Nontrivial V]
    (R : SimpleGraph V) (htree : R.IsTree) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hleaves : ∀ x, TreeLeaf R x → x ≠ root → twoPendantCore V a b x ∈ C) :
    ∀ x, twoPendantCore V a b x ∈
      colorAfter (twoPendantGraph R root a b).Adj C (Fintype.card V) := by
  classical
  let L := Finset.univ.filter (fun x => TreeLeaf R x ∧ x ≠ root)
  apply rooted_leaf_embedding_colors_image R htree root
    (twoPendantGraph R root a b) (twoPendantCore V a b) (fun h => h)
    ?_ L C ?_ ?_
  · intro x hxr z hz
    rcases z with y | (i | j)
    · exact ⟨y, rfl, hz⟩
    · exact False.elim (hxr hz.1)
    · exact False.elim (hxr hz.1)
  · intro x hx hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hm⟩
  · intro x hx
    have hx' : TreeLeaf R x ∧ x ≠ root := (Finset.mem_filter.mp hx).2
    exact hleaves x hx'.1 hx'.2

theorem twoPendant_heads_in_step (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hc : ∀ x, twoPendantCore V a b x ∈ C)
    (hh : twoPendantA V a b 0 ∈ C ∨ twoPendantB V a b 0 ∈ C) :
    twoPendantA V a b 0 ∈ synchronousStep (twoPendantGraph R root a b).Adj C ∧
      twoPendantB V a b 0 ∈ synchronousStep (twoPendantGraph R root a b).Adj C := by
  classical
  constructor
  · rcases hh with hA | hB
    · exact subset_synchronousStep _ _ hA
    · apply (mem_synchronousStep _ _ _).mpr
      refine Or.inr ⟨twoPendantCore V a b root, hc root, ⟨rfl, rfl⟩, ?_⟩
      intro other ho hw
      rcases other with x | (i | j)
      · exact False.elim (hw (hc x))
      · change root = root ∧ i = 0 at ho
        exact congrArg (twoPendantA V a b) ho.2
      · change root = root ∧ j = 0 at ho
        exact False.elim (hw (ho.2 ▸ hB))
  · rcases hh with hA | hB
    · apply (mem_synchronousStep _ _ _).mpr
      refine Or.inr ⟨twoPendantCore V a b root, hc root, ⟨rfl, rfl⟩, ?_⟩
      intro other ho hw
      rcases other with x | (i | j)
      · exact False.elim (hw (hc x))
      · change root = root ∧ i = 0 at ho
        exact False.elim (hw (ho.2 ▸ hA))
      · change root = root ∧ j = 0 at ho
        exact congrArg (twoPendantB V a b) ho.2
    · exact subset_synchronousStep _ _ hB

theorem twoPendant_forcing_of_core_and_head (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hc : ∀ x, twoPendantCore V a b x ∈ C)
    (hh : twoPendantA V a b 0 ∈ C ∨ twoPendantB V a b 0 ∈ C) :
    IsForcing (twoPendantGraph R root a b).Adj C := by
  classical
  let G := twoPendantGraph R root a b
  let C' := synchronousStep G.Adj C
  have hheads := twoPendant_heads_in_step R root a b C hc hh
  have hc' : ∀ x, twoPendantCore V a b x ∈ C' :=
    fun x => subset_synchronousStep G.Adj C (hc x)
  have hA := twoPendant_armA_colors R root a b C' (hc' root) hheads.1
  have hB := twoPendant_armB_colors R root a b C' (hc' root) hheads.2
  apply IsForcing_of_forcing_colorAfter G.Adj C 1
  refine ⟨max (a + 1) (b + 1), Finset.eq_univ_of_forall ?_⟩
  rintro (x | (i | j))
  · exact colorAfter_mono_time G.Adj C' (Nat.zero_le _) (hc' x)
  · exact colorAfter_mono_time G.Adj C' (le_max_left _ _) (hA i)
  · exact colorAfter_mono_time G.Adj C' (le_max_right _ _) (hB j)

end FaultObservationResearch
