module

/-
The all-long-arm witness coloring: all heads, plus the second vertex on two arms.
The specified two-point deletion leaves the already verified fixed head coloring.
Cardinality-minimality and the time separation are proved separately.
-/
public import «formalization-path-star-blocked»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

def pathStarHead (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i) (i : I) :
    PathStarVertex I lengths := some ⟨i, ⟨0, by have h := hlong i; omega⟩⟩

def pathStarSecond (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i) (i : I) :
    PathStarVertex I lengths := some ⟨i, ⟨1, by have h := hlong i; omega⟩⟩

def pathStarPairSupport (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i) (a b : I) :
    Finset (PathStarVertex I lengths) :=
  {pathStarSecond lengths hlong a, pathStarSecond lengths hlong b}

def pathStarPairInitial (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i) (a b : I) :
    Finset (PathStarVertex I lengths) :=
  pathStarHeads lengths ∪ pathStarPairSupport lengths hlong a b

omit [Fintype I] [DecidableEq I] in
theorem pathStar_arm_index_ne (lengths : I → ℕ) {i j : I} (hne : i ≠ j)
    (k : Fin (lengths i)) (l : Fin (lengths j)) :
    (some ⟨i, k⟩ : PathStarVertex I lengths) ≠ some ⟨j, l⟩ := by
  intro h
  have hi := congrArg (Option.map (fun z : Σ i, Fin (lengths i) => z.1)) h
  exact hne (Option.some.inj hi)

omit [Fintype I] [DecidableEq I] in
theorem pathStar_head_ne_second (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i)
    (i j : I) (k : Fin (lengths i)) (hk : k.val = 0) :
    (some ⟨i, k⟩ : PathStarVertex I lengths) ≠ pathStarSecond lengths hlong j := by
  intro h
  have hv := congrArg (Option.map (fun z : Σ i, Fin (lengths i) => z.2.val)) h
  change some k.val = some 1 at hv
  have hval := Option.some.inj hv
  omega

omit [Fintype I] in
theorem pathStar_pair_support_card (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i)
    (a b : I) (hab : a ≠ b) : (pathStarPairSupport lengths hlong a b).card = 2 := by
  apply Finset.card_pair_eq_two_iff.mpr
  exact pathStar_arm_index_ne lengths hab _ _

omit [Fintype I] in
theorem pathStar_head_not_support (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i)
    (a b i : I) (k : Fin (lengths i)) (hk : k.val = 0) :
    some ⟨i, k⟩ ∉ pathStarPairSupport lengths hlong a b := by
  have ha := pathStar_head_ne_second lengths hlong i a k hk
  have hb := pathStar_head_ne_second lengths hlong i b k hk
  simp [pathStarPairSupport, ha, hb]

theorem pathStar_initial_sdiff_support (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i)
    (a b : I) : pathStarPairInitial lengths hlong a b \ pathStarPairSupport lengths hlong a b =
      pathStarHeads lengths := by
  classical
  ext vertex
  simp only [pathStarPairInitial, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hhead | hsupport, hnot⟩
    · exact hhead
    · exact False.elim (hnot hsupport)
  · intro hhead
    refine ⟨Or.inl hhead, ?_⟩
    cases vertex with
    | none => simp [pathStarHeads] at hhead
    | some vertex =>
      obtain ⟨i, k⟩ := vertex
      have hk : k.val = 0 := by simpa [pathStarHeads] using hhead
      exact pathStar_head_not_support lengths hlong a b i k hk

theorem pathStar_support_subset_initial (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i)
    (a b : I) : pathStarPairSupport lengths hlong a b ⊆ pathStarPairInitial lengths hlong a b := by
  intro vertex hv
  exact Finset.mem_union_right _ hv

theorem pathStar_center_not_initial (lengths : I → ℕ) (hlong : ∀ i, 2 ≤ lengths i)
    (a b : I) : (none : PathStarVertex I lengths) ∉ pathStarPairInitial lengths hlong a b := by
  simp [pathStarPairInitial, pathStarHeads, pathStarPairSupport, pathStarSecond]

end FaultObservationResearch
