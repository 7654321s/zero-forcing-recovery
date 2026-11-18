module

public import «formalization-foundations»

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

universe u v

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Join two disjoint graphs by the edge between root and head. -/
def attachAtAdj (core : V → V → Prop) (tail : W → W → Prop)
    (root : V) (head : W) : V ⊕ W → V ⊕ W → Prop
  | .inl x, .inl y => core x y
  | .inr x, .inr y => tail x y
  | .inl x, .inr y => x = root ∧ y = head
  | .inr x, .inl y => x = head ∧ y = root

/-- The attachment preserves one round on the old vertices if the head neither
blocks a necessary old force nor supplies an earlier force into the root. -/
theorem attachAt_core_step (core : V → V → Prop) (tail : W → W → Prop)
    (root : V) (head : W) (old : Finset V) (large : Finset (V ⊕ W))
    (same : ∀ x, Sum.inl x ∈ large ↔ x ∈ old)
    (outgoing : root ∈ old → Sum.inr head ∈ large ∨ ∀ y, core root y → y ∈ old)
    (incoming : Sum.inr head ∈ large →
      (∀ y, tail head y → Sum.inr y ∈ large) → root ∈ synchronousStep core old)
    (x : V) :
    Sum.inl x ∈ synchronousStep (attachAtAdj core tail root head) large ↔
      x ∈ synchronousStep core old := by
  rw [mem_synchronousStep, mem_synchronousStep]
  constructor
  · rintro (hx | ⟨source, hs, ha, hu⟩)
    · exact Or.inl ((same x).mp hx)
    · cases source with
      | inl source =>
        refine Or.inr ⟨source, (same source).mp hs, ha, ?_⟩
        intro y hy hyWhite
        exact Sum.inl.inj (hu (.inl y) hy (fun h => hyWhite ((same y).mp h)))
      | inr source =>
        change source = head ∧ x = root at ha
        obtain ⟨hsource, hx⟩ := ha
        subst source
        subst x
        have h := incoming hs (by
          intro y hy
          by_contra hn
          have hImpossible : (Sum.inr y : V ⊕ W) = Sum.inl root := hu (.inr y) hy hn
          cases hImpossible)
        exact (mem_synchronousStep core old root).mp h
  · rintro (hx | ⟨source, hs, ha, hu⟩)
    · exact Or.inl ((same x).mpr hx)
    · by_cases hx : x ∈ old
      · exact Or.inl ((same x).mpr hx)
      refine Or.inr ⟨.inl source, (same source).mpr hs, ha, ?_⟩
      intro y hy hyWhite
      cases y with
      | inl y =>
        exact congrArg Sum.inl (hu y hy (fun h => hyWhite ((same y).mpr h)))
      | inr y =>
        change source = root ∧ y = head at hy
        obtain ⟨rfl, rfl⟩ := hy
        exact False.elim ((outgoing hs).elim hyWhite (fun h => hx (h x ha)))

/-- For a blue attachment, restoration of the root by round one suffices for
exact projection at every round in the compared coloring. Only its head needs
to be blue for projection. -/
theorem attachAt_core_colorAfter_of_blue_head (core : V → V → Prop)
    (tail : W → W → Prop) (root : V) (head : W)
    (old : Finset V) (large : Finset (V ⊕ W))
    (same : ∀ x, Sum.inl x ∈ large ↔ x ∈ old) (headBlue : Sum.inr head ∈ large)
    (rootByOne : root ∈ colorAfter core old 1) :
    ∀ t x, Sum.inl x ∈ colorAfter (attachAtAdj core tail root head) large t ↔
      x ∈ colorAfter core old t := by
  intro t
  induction t with
  | zero => exact same
  | succ t ih =>
    intro x
    apply attachAt_core_step core tail root head _ _ ih
    · intro _
      exact Or.inl (colorAfter_mono_time _ _ (Nat.zero_le t) headBlue)
    · intro _ _
      exact colorAfter_mono_time _ _ (by omega : 1 ≤ t + 1) rootByOne

/-- A stalled branch has its initial coloring on all rounds up to and
including the first round in which the root becomes blue. Projection is exact
for the old graph. The condition on the old neighbors covers a white tail at
a leaf, and is vacuous for a blue head on a side path. -/
theorem attachAt_core_and_stalled_tail (core : V → V → Prop)
    (tail : W → W → Prop) (root : V) (head : W)
    (old : Finset V) (initialTail : Finset W) (large : Finset (V ⊕ W))
    (sameOld : ∀ x, Sum.inl x ∈ large ↔ x ∈ old)
    (sameTail : ∀ y, Sum.inr y ∈ large ↔ y ∈ initialTail)
    (fixed : synchronousStep (fun x y => x ≠ head ∧ tail x y) initialTail = initialTail)
    (blocked : head ∈ initialTail → ∃ y, tail head y ∧ y ∉ initialTail)
    (outgoing : ∀ t, root ∈ colorAfter core old t →
      head ∈ initialTail ∨ ∀ x, core root x → x ∈ colorAfter core old t) :
    ∀ t,
      (∀ x, Sum.inl x ∈ colorAfter (attachAtAdj core tail root head) large t ↔
        x ∈ colorAfter core old t) ∧
      ((∀ s < t, root ∉ colorAfter core old s) → ∀ y,
        Sum.inr y ∈ colorAfter (attachAtAdj core tail root head) large t ↔
          y ∈ initialTail) := by
  let joined := attachAtAdj core tail root head
  have firstBlue : ∀ y ∈ initialTail, ∀ t, Sum.inr y ∈ colorAfter joined large t := by
    intro y hy t
    exact colorAfter_mono_time joined large (Nat.zero_le t) ((sameTail y).mpr hy)
  intro t
  induction t with
  | zero => exact ⟨sameOld, fun _ => sameTail⟩
  | succ t ih =>
    refine ⟨?_, ?_⟩
    · intro x
      apply attachAt_core_step core tail root head _ _ ih.1
      · intro hroot
        exact (outgoing t hroot).imp (fun h => firstBlue head h t) id
      · intro hh hAll
        by_cases hroot : root ∈ colorAfter core old t
        · exact subset_synchronousStep core _ hroot
        · have hBefore : ∀ s < t, root ∉ colorAfter core old s :=
            fun s hs h => hroot (colorAfter_mono_time core old (Nat.le_of_lt hs) h)
          have hHead := (ih.2 hBefore head).mp hh
          obtain ⟨y, hy, hWhite⟩ := blocked hHead
          exact False.elim (hWhite ((ih.2 hBefore y).mp (hAll y hy)))
    · intro hBefore y
      have hBeforeT : ∀ s < t, root ∉ colorAfter core old s :=
        fun s hs => hBefore s (by omega)
      constructor
      · intro hy
        rcases (mem_synchronousStep joined (colorAfter joined large t) (.inr y)).mp hy with
          hyBlue | ⟨source, hs, ha, hu⟩
        · exact (ih.2 hBeforeT y).mp hyBlue
        · cases source with
          | inl x =>
            change x = root ∧ y = head at ha
            exact False.elim (hBefore t (by omega) (ha.1 ▸ (ih.1 x).mp hs))
          | inr x =>
            have hNotHead : x ≠ head := by
              intro h
              subst x
              have hWhite : Sum.inl root ∉ colorAfter joined large t :=
                fun hz => hBefore t (by omega) ((ih.1 root).mp hz)
              have hImpossible : (Sum.inl root : V ⊕ W) = Sum.inr y :=
                hu (.inl root) ⟨rfl, rfl⟩ hWhite
              cases hImpossible
            rw [← fixed]
            apply (mem_synchronousStep (fun x z => x ≠ head ∧ tail x z) initialTail y).mpr
            refine Or.inr ⟨x, (ih.2 hBeforeT x).mp hs, ⟨hNotHead, ha⟩, ?_⟩
            intro z hz hw
            exact Sum.inr.inj (hu (.inr z) hz.2 (fun h => hw ((ih.2 hBeforeT z).mp h)))
      · intro hy
        exact firstBlue y hy (t + 1)

/-- Once an initially white degree-one root turns blue, its old neighbor
has already turned blue. -/
theorem leaf_neighbor_blue_after_restoration (core : V → V → Prop)
    (symmetric : ∀ ⦃x y⦄, core x y → core y x) (old : Finset V) (root neighbor : V)
    (unique : ∀ x, core root x → x = neighbor) (white : root ∉ old) :
    ∀ t, root ∈ colorAfter core old t → neighbor ∈ colorAfter core old t := by
  intro t
  induction t with
  | zero => exact fun h => False.elim (white h)
  | succ t ih =>
    intro h
    rcases (mem_synchronousStep core (colorAfter core old t) root).mp h with
      hAlready | ⟨source, hSource, hAdj, _⟩
    · exact colorAfter_subset_succ core old t (ih hAlready)
    · exact colorAfter_subset_succ core old t
        (unique source (symmetric hAdj) ▸ hSource)

/-- The attached part evolves by its own rule once both ends of the bridge
are blue. -/
theorem attachAt_tail_step_of_blue_bridge (core : V → V → Prop)
    (tail : W → W → Prop) (root : V) (head : W)
    (large : Finset (V ⊕ W)) (tailBlue : Finset W)
    (same : ∀ w, Sum.inr w ∈ large ↔ w ∈ tailBlue)
    (rootBlue : Sum.inl root ∈ large) (headBlue : head ∈ tailBlue) (w : W) :
    Sum.inr w ∈ synchronousStep (attachAtAdj core tail root head) large ↔
      w ∈ synchronousStep tail tailBlue := by
  rw [mem_synchronousStep, mem_synchronousStep]
  constructor
  · rintro (hw | ⟨source, hs, ha, hu⟩)
    · exact Or.inl ((same w).mp hw)
    · cases source with
      | inl source =>
        change source = root ∧ w = head at ha
        exact Or.inl (ha.2.symm ▸ headBlue)
      | inr source =>
        refine Or.inr ⟨source, (same source).mp hs, ha, ?_⟩
        intro y hy hyWhite
        exact Sum.inr.inj (hu (.inr y) hy (fun h => hyWhite ((same y).mp h)))
  · rintro (hw | ⟨source, hs, ha, hu⟩)
    · exact Or.inl ((same w).mpr hw)
    · refine Or.inr ⟨.inr source, (same source).mpr hs, ha, ?_⟩
      intro y hy hyWhite
      cases y with
      | inl y =>
        change source = head ∧ y = root at hy
        exact False.elim (hyWhite (hy.2.symm ▸ rootBlue))
      | inr y =>
        exact congrArg Sum.inr (hu y hy (fun h => hyWhite ((same y).mpr h)))

theorem attachAt_tail_colorAfter_of_blue_bridge (core : V → V → Prop)
    (tail : W → W → Prop) (root : V) (head : W)
    (large : Finset (V ⊕ W)) (tailBlue : Finset W)
    (same : ∀ w, Sum.inr w ∈ large ↔ w ∈ tailBlue)
    (rootBlue : Sum.inl root ∈ large) (headBlue : head ∈ tailBlue) :
    ∀ t w, Sum.inr w ∈ colorAfter (attachAtAdj core tail root head) large t ↔
      w ∈ colorAfter tail tailBlue t := by
  intro t
  induction t with
  | zero => exact same
  | succ t ih =>
    intro w
    exact attachAt_tail_step_of_blue_bridge core tail root head _ _ ih
      (colorAfter_mono_time _ _ (Nat.zero_le t) rootBlue)
      (colorAfter_mono_time _ _ (Nat.zero_le t) headBlue) w

/-- Activation of a wholly white tail colors exactly its head in one round. -/
theorem attachAt_step_starts_white_tail (core : V → V → Prop)
    (tail : W → W → Prop) (root : V) (head : W)
    (large : Finset (V ⊕ W)) (rootBlue : Sum.inl root ∈ large)
    (neighborsBlue : ∀ x, core root x → Sum.inl x ∈ large)
    (tailWhite : ∀ w, Sum.inr w ∉ large) (w : W) :
    Sum.inr w ∈ synchronousStep (attachAtAdj core tail root head) large ↔ w = head := by
  rw [mem_synchronousStep]
  constructor
  · rintro (hw | ⟨source, hs, ha, _⟩)
    · exact False.elim (tailWhite w hw)
    · cases source with
      | inl x => exact ha.2
      | inr x => exact False.elim (tailWhite x hs)
  · rintro rfl
    refine Or.inr ⟨.inl root, rootBlue, ⟨rfl, rfl⟩, ?_⟩
    intro other ha hw
    cases other with
    | inl x => exact False.elim (hw (neighborsBlue x ha))
    | inr x => exact congrArg Sum.inr ha.2

/-- Split completion into completion of the core and of the attachment. -/
theorem attachAt_finishesBy_iff (core : V → V → Prop) (tail : W → W → Prop)
    (root : V) (head : W) (old : Finset V) (large : Finset (V ⊕ W)) (t : ℕ)
    (same : ∀ x, Sum.inl x ∈ colorAfter (attachAtAdj core tail root head) large t ↔
      x ∈ colorAfter core old t) :
    FinishesBy (attachAtAdj core tail root head) large t ↔
      FinishesBy core old t ∧
        ∀ w, Sum.inr w ∈ colorAfter (attachAtAdj core tail root head) large t := by
  constructor
  · intro h
    have hBlue : ∀ w, w ∈ colorAfter (attachAtAdj core tail root head) large t := by
      rw [show colorAfter _ _ _ = Finset.univ from h]
      exact Finset.mem_univ
    exact ⟨Finset.eq_univ_of_forall (fun x => (same x).mp (hBlue (.inl x))),
      fun w => hBlue (.inr w)⟩
  · rintro ⟨hOld, hSide⟩
    apply Finset.eq_univ_of_forall
    intro w
    cases w with
    | inl x =>
      apply (same x).mpr
      rw [show colorAfter _ _ _ = Finset.univ from hOld]
      exact Finset.mem_univ _
    | inr x => exact hSide x

/-- With all new vertices blue and restoration of the old root by round one,
the attachment leaves the completion time unchanged. -/
theorem all_blue_attachment_finishesBy_iff (core : V → V → Prop) (tail : W → W → Prop)
    (root : V) (head : W) (old : Finset V) (large : Finset (V ⊕ W)) (t : ℕ)
    (same : ∀ x, Sum.inl x ∈ large ↔ x ∈ old) (allTail : ∀ w, Sum.inr w ∈ large)
    (rootByOne : root ∈ colorAfter core old 1) :
    FinishesBy (attachAtAdj core tail root head) large t ↔ FinishesBy core old t := by
  rw [attachAt_finishesBy_iff core tail root head old large t
    (attachAt_core_colorAfter_of_blue_head core tail root head old large same (allTail head)
      rootByOne t)]
  exact and_iff_left (fun w => colorAfter_mono_time _ _ (Nat.zero_le t) (allTail w))

/-- The projection includes all forces from the core, either with a blue
head or with forces from the root suppressed. -/
theorem attachAt_contains_core (core : V → V → Prop) (tail : W → W → Prop)
    (root : V) (head : W) (old : Finset V) (large : Finset (V ⊕ W))
    (allowRoot : Prop) (unblocked : allowRoot → Sum.inr head ∈ large)
    (same : ∀ x ∈ old, Sum.inl x ∈ large) :
    ∀ t x, x ∈ colorAfter (fun s y => core s y ∧ (s ≠ root ∨ allowRoot)) old t →
      Sum.inl x ∈ colorAfter (attachAtAdj core tail root head) large t := by
  intro t
  induction t with
  | zero => exact same
  | succ t ih =>
    intro x hx
    apply (mem_synchronousStep _ _ _).mpr
    rcases (mem_synchronousStep _ _ _).mp hx with hx | ⟨source, hs, ha, hu⟩
    · exact Or.inl (ih x hx)
    · refine Or.inr ⟨.inl source, ih source hs, ha.1, ?_⟩
      intro z hz hw
      cases z with
      | inl z =>
        exact congrArg Sum.inl (hu z ⟨hz, ha.2⟩ (fun h => hw (ih z h)))
      | inr z =>
        change source = root ∧ z = head at hz
        rcases ha.2 with h | h
        · exact False.elim (h hz.1)
        · exact False.elim (hw (hz.2.symm ▸
            colorAfter_mono_time _ _ (Nat.zero_le t) (unblocked h)))

end FaultObservationResearch

#print axioms FaultObservationResearch.attachAt_core_colorAfter_of_blue_head
#print axioms FaultObservationResearch.attachAt_core_and_stalled_tail
#print axioms FaultObservationResearch.leaf_neighbor_blue_after_restoration
#print axioms FaultObservationResearch.attachAt_tail_colorAfter_of_blue_bridge
#print axioms FaultObservationResearch.attachAt_step_starts_white_tail
#print axioms FaultObservationResearch.all_blue_attachment_finishesBy_iff
#print axioms FaultObservationResearch.attachAt_contains_core
