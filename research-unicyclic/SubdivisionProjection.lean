module

public import «formalization-foundations»

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch

universe u v

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def replacesEdge {V : Type u} (x y a b : V) : Prop :=
  (a = x ∧ b = y) ∨ (a = y ∧ b = x)

/-- Replace the old edge with a new part attached only at its two ends.
For one inserted vertex, the two attachment points coincide. -/
def subdivideAdj (old : V → V → Prop) (new : W → W → Prop)
    (x y : V) (first last : W) : V ⊕ W → V ⊕ W → Prop
  | .inl a, .inl b => old a b ∧ ¬ replacesEdge x y a b
  | .inr a, .inr b => new a b
  | .inl a, .inr b => (a = x ∧ b = first) ∨ (a = y ∧ b = last)
  | .inr a, .inl b => (b = x ∧ a = first) ∨ (b = y ∧ a = last)

omit [Fintype V] [DecidableEq V] in
theorem replacesEdge_right_blue {x y a b : V} {blue : Finset V}
    (hx : x ∈ blue) (hy : y ∈ blue) (h : replacesEdge x y a b) : b ∈ blue :=
  h.elim (fun hxy => hxy.2.symm ▸ hy) (fun hyx => hyx.2.symm ▸ hx)

/-- With the old endpoints and the inserted vertices all blue, the deleted
edge and its replacement contribute no white neighbor to any old source. -/
theorem subdivide_core_step (old : V → V → Prop) (new : W → W → Prop)
    (x y : V) (first last : W) (blue : Finset V) (large : Finset (V ⊕ W))
    (same : ∀ a, Sum.inl a ∈ large ↔ a ∈ blue)
    (hx : x ∈ blue) (hy : y ∈ blue) (newBlue : ∀ q, Sum.inr q ∈ large) (b : V) :
    Sum.inl b ∈ synchronousStep (subdivideAdj old new x y first last) large ↔
      b ∈ synchronousStep old blue := by
  rw [mem_synchronousStep, mem_synchronousStep]
  constructor
  · rintro (hb | ⟨source, hs, ha, hu⟩)
    · exact Or.inl ((same b).mp hb)
    · cases source with
      | inl a =>
        change old a b ∧ ¬ replacesEdge x y a b at ha
        refine Or.inr ⟨a, (same a).mp hs, ha.1, ?_⟩
        intro c hc hcWhite
        have hKeep : ¬ replacesEdge x y a c :=
          fun h => hcWhite (replacesEdge_right_blue hx hy h)
        exact Sum.inl.inj (hu (.inl c) ⟨hc, hKeep⟩ (fun h => hcWhite ((same c).mp h)))
      | inr a =>
        change (b = x ∧ a = first) ∨ (b = y ∧ a = last) at ha
        exact Or.inl (ha.elim (fun h => h.1.symm ▸ hx) (fun h => h.1.symm ▸ hy))
  · rintro (hb | ⟨a, ha, hab, hu⟩)
    · exact Or.inl ((same b).mpr hb)
    · by_cases hb : b ∈ blue
      · exact Or.inl ((same b).mpr hb)
      have hKeep : ¬ replacesEdge x y a b :=
        fun h => hb (replacesEdge_right_blue hx hy h)
      refine Or.inr ⟨.inl a, (same a).mpr ha, ⟨hab, hKeep⟩, ?_⟩
      intro c hc hcWhite
      cases c with
      | inl c =>
        change old a c ∧ ¬ replacesEdge x y a c at hc
        exact congrArg Sum.inl (hu c hc.1 (fun h => hcWhite ((same c).mpr h)))
      | inr c =>
        exact False.elim (hcWhite (newBlue c))

theorem subdivide_core_colorAfter (old : V → V → Prop) (new : W → W → Prop)
    (x y : V) (first last : W) (blue : Finset V) (large : Finset (V ⊕ W))
    (same : ∀ a, Sum.inl a ∈ large ↔ a ∈ blue)
    (hx : x ∈ blue) (hy : y ∈ blue) (newBlue : ∀ q, Sum.inr q ∈ large) :
    ∀ t b, Sum.inl b ∈ colorAfter (subdivideAdj old new x y first last) large t ↔
      b ∈ colorAfter old blue t := by
  intro t
  induction t with
  | zero => exact same
  | succ t ih =>
    intro b
    exact subdivide_core_step old new x y first last _ _ ih
      (colorAfter_mono_time _ _ (Nat.zero_le t) hx)
      (colorAfter_mono_time _ _ (Nat.zero_le t) hy)
      (fun q => colorAfter_mono_time _ _ (Nat.zero_le t) (newBlue q)) b

theorem subdivide_finishesBy_iff (old : V → V → Prop) (new : W → W → Prop)
    (x y : V) (first last : W) (blue : Finset V) (large : Finset (V ⊕ W))
    (same : ∀ a, Sum.inl a ∈ large ↔ a ∈ blue)
    (hx : x ∈ blue) (hy : y ∈ blue) (newBlue : ∀ q, Sum.inr q ∈ large) (t : ℕ) :
    FinishesBy (subdivideAdj old new x y first last) large t ↔ FinishesBy old blue t := by
  have hCore := subdivide_core_colorAfter old new x y first last blue large same hx hy newBlue t
  constructor
  · intro h
    apply Finset.eq_univ_of_forall
    intro b
    apply (hCore b).mp
    rw [show colorAfter _ _ _ = Finset.univ from h]
    exact Finset.mem_univ _
  · intro h
    apply Finset.eq_univ_of_forall
    intro q
    cases q with
    | inl b =>
      apply (hCore b).mpr
      rw [show colorAfter _ _ _ = Finset.univ from h]
      exact Finset.mem_univ _
    | inr b =>
      exact colorAfter_mono_time _ _ (Nat.zero_le t) (newBlue b)

/-- The endpoint that survives suffices to allow an inserted vertex to
restore the other endpoint in one round. -/
theorem subdivide_restore_endpoint (old : V → V → Prop) (new : W → W → Prop)
    (x y : V) (first last : W) (large : Finset (V ⊕ W)) (b : V)
    (endpoint : b = x ∨ b = y)
    (otherBlue : ∀ a, (a = x ∨ a = y) → a ≠ b → Sum.inl a ∈ large)
    (allNew : ∀ q, Sum.inr q ∈ large) :
    Sum.inl b ∈ synchronousStep (subdivideAdj old new x y first last) large := by
  rcases endpoint with hx | hy
  · subst b
    apply (mem_synchronousStep _ _ _).mpr
    refine Or.inr ⟨.inr first, allNew first, Or.inl ⟨rfl, rfl⟩, ?_⟩
    intro a ha haWhite
    cases a with
    | inl a =>
      change (a = x ∧ first = first) ∨ (a = y ∧ first = last) at ha
      by_contra h
      exact haWhite (otherBlue a (ha.imp And.left And.left)
        (fun eq => h (congrArg Sum.inl eq)))
    | inr a =>
      exact False.elim (haWhite (allNew a))
  · subst b
    apply (mem_synchronousStep _ _ _).mpr
    refine Or.inr ⟨.inr last, allNew last, Or.inr ⟨rfl, rfl⟩, ?_⟩
    intro a ha haWhite
    cases a with
    | inl a =>
      change (a = x ∧ last = first) ∨ (a = y ∧ last = last) at ha
      by_contra h
      exact haWhite (otherBlue a (ha.imp And.left And.left)
        (fun eq => h (congrArg Sum.inl eq)))
    | inr a =>
      exact False.elim (haWhite (allNew a))

/-- A surviving inserted neighbor can repair a lost inserted vertex in
round one. The old endpoints are blue. -/
theorem subdivide_restore_new_from_new (old : V → V → Prop) (new : W → W → Prop)
    (x y : V) (first last : W) (large : Finset (V ⊕ W)) (q source : W)
    (hx : Sum.inl x ∈ large) (hy : Sum.inl y ∈ large)
    (newSurvives : ∀ w, w ≠ q → Sum.inr w ∈ large)
    (sourceSurvives : source ≠ q) (adjacent : new source q) :
    Sum.inr q ∈ synchronousStep (subdivideAdj old new x y first last) large := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨.inr source, newSurvives source sourceSurvives, adjacent, ?_⟩
  intro a ha haWhite
  cases a with
  | inl b =>
    change (b = x ∧ source = first) ∨ (b = y ∧ source = last) at ha
    exact False.elim (haWhite (ha.elim (fun h => h.1.symm ▸ hx) (fun h => h.1.symm ▸ hy)))
  | inr b =>
    by_contra h
    exact haWhite (newSurvives b (fun eq => h (congrArg Sum.inr eq)))

/-- For a single inserted vertex, an endpoint with all its old neighbors
blue restores it in one round. -/
theorem subdivide_restore_from_left_endpoint
    (old : V → V → Prop) (new : W → W → Prop) (x y : V) (first last : W)
    (large : Finset (V ⊕ W)) (hx : Sum.inl x ∈ large) (distinct : x ≠ y)
    (neighborsBlue : ∀ a, old x a → Sum.inl a ∈ large) :
    Sum.inr first ∈ synchronousStep (subdivideAdj old new x y first last) large := by
  apply (mem_synchronousStep _ _ _).mpr
  refine Or.inr ⟨.inl x, hx, Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro a ha haWhite
  cases a with
  | inl b =>
    change old x b ∧ ¬ replacesEdge x y x b at ha
    exact False.elim (haWhite (neighborsBlue b ha.1))
  | inr b =>
    change (x = x ∧ b = first) ∨ (x = y ∧ b = last) at ha
    exact ha.elim (fun h => congrArg Sum.inr h.2) (fun h => False.elim (distinct h.1))

end FaultObservationResearch

#print axioms FaultObservationResearch.subdivide_finishesBy_iff
#print axioms FaultObservationResearch.subdivide_restore_endpoint
#print axioms FaultObservationResearch.subdivide_restore_new_from_new
#print axioms FaultObservationResearch.subdivide_restore_from_left_endpoint
