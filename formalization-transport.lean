module

/-
Relabeling invariance for the synchronous initial-color-loss model.
These are formal proof-transport tools, not claims of research novelty.
-/
public import «formalization-foundations»

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FaultObservationResearch

universe u v

variable {V : Type u} {W : Type v}

def relabelColors (e : V ≃ W) (blue : Finset V) : Finset W :=
  blue.map e.toEmbedding

@[simp] theorem mem_relabelColors (e : V ≃ W) (blue : Finset V) (w : W) :
    w ∈ relabelColors e blue ↔ e.symm w ∈ blue :=
  Finset.mem_map_equiv

@[simp] theorem relabelColors_card (e : V ≃ W) (blue : Finset V) :
    (relabelColors e blue).card = blue.card := by simp [relabelColors]

@[simp] theorem relabelColors_symm (e : V ≃ W) (blue : Finset V) :
    relabelColors e.symm (relabelColors e blue) = blue := by
  ext x
  simp

@[simp] theorem relabelColors_apply_symm (e : V ≃ W) (blue : Finset W) :
    relabelColors e (relabelColors e.symm blue) = blue := by
  simpa only [Equiv.symm_symm] using relabelColors_symm e.symm blue

theorem relabelColors_subset_iff (e : V ≃ W) (A B : Finset V) :
    relabelColors e A ⊆ relabelColors e B ↔ A ⊆ B :=
  Finset.map_subset_map

theorem relabelColors_sdiff [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (blue loss : Finset V) :
    relabelColors e (blue \ loss) = relabelColors e blue \ relabelColors e loss :=
  Finset.map_sdiff blue loss

@[simp] theorem relabelColors_univ [Fintype V] [Fintype W] (e : V ≃ W) :
    relabelColors e Finset.univ = Finset.univ := by
  ext w
  simp

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem synchronousStep_relabel (e : V ≃ W)
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (hadj : ∀ x y, adjW (e x) (e y) ↔ adjV x y) (blue : Finset V) :
    relabelColors e (synchronousStep adjV blue) =
      synchronousStep adjW (relabelColors e blue) := by
  classical
  apply Finset.ext
  intro w
  obtain ⟨target, rfl⟩ := e.surjective w
  rw [mem_relabelColors, Equiv.symm_apply_apply]
  constructor
  · intro h
    apply (mem_synchronousStep _ _ _).mpr
    rcases (mem_synchronousStep _ _ _).mp h with hold | ⟨source, hs, ha, hu⟩
    · exact Or.inl (by simpa using hold)
    · refine Or.inr ⟨e source, by simpa using hs, (hadj source target).mpr ha, ?_⟩
      intro other hao hwhite
      have haV : adjV source (e.symm other) := (hadj source _).mp (by simpa using hao)
      have hwV : e.symm other ∉ blue := by simpa using hwhite
      have heq := hu (e.symm other) haV hwV
      calc
        other = e (e.symm other) := (e.apply_symm_apply other).symm
        _ = e target := congrArg e heq
  · intro h
    apply (mem_synchronousStep _ _ _).mpr
    rcases (mem_synchronousStep _ _ _).mp h with hold | ⟨source, hs, ha, hu⟩
    · exact Or.inl (by simpa using hold)
    · obtain ⟨sourceV, rfl⟩ := e.surjective source
      refine Or.inr ⟨sourceV, by simpa using hs, (hadj sourceV target).mp ha, ?_⟩
      intro other hao hwhite
      have hwW : e other ∉ relabelColors e blue := by simpa using hwhite
      exact e.injective (hu (e other) ((hadj sourceV other).mpr hao) hwW)

theorem colorAfter_relabel (e : V ≃ W)
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (hadj : ∀ x y, adjW (e x) (e y) ↔ adjV x y) (blue : Finset V) (t : ℕ) :
    relabelColors e (colorAfter adjV blue t) = colorAfter adjW (relabelColors e blue) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change relabelColors e (synchronousStep adjV (colorAfter adjV blue t)) =
      synchronousStep adjW (colorAfter adjW (relabelColors e blue) t)
    rw [synchronousStep_relabel e adjV adjW hadj, ih]

theorem FinishesBy_relabel_iff (e : V ≃ W)
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (hadj : ∀ x y, adjW (e x) (e y) ↔ adjV x y) (blue : Finset V) (t : ℕ) :
    FinishesBy adjW (relabelColors e blue) t ↔ FinishesBy adjV blue t := by
  unfold FinishesBy
  rw [← colorAfter_relabel e adjV adjW hadj, ← relabelColors_univ e]
  exact Finset.map_inj

theorem IsForcing_relabel_iff (e : V ≃ W)
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (hadj : ∀ x y, adjW (e x) (e y) ↔ adjV x y) (blue : Finset V) :
    IsForcing adjW (relabelColors e blue) ↔ IsForcing adjV blue := by
  simp only [IsForcing, FinishesBy_relabel_iff e adjV adjW hadj]

theorem IsMinimumKilling_relabel_iff (e : V ≃ W)
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (hadj : ∀ x y, adjW (e x) (e y) ↔ adjV x y) (blue support : Finset V) :
    IsMinimumKilling adjW (relabelColors e blue) (relabelColors e support) ↔
      IsMinimumKilling adjV blue support := by
  constructor
  · rintro ⟨hsub, hfail, hmin⟩
    refine ⟨(relabelColors_subset_iff e _ _).mp hsub, ?_, ?_⟩
    · intro hf
      apply hfail
      rw [← relabelColors_sdiff]
      exact (IsForcing_relabel_iff e adjV adjW hadj _).mpr hf
    · intro loss hloss hcard
      have hsubW := (relabelColors_subset_iff e _ _).mpr hloss
      have hcardW : (relabelColors e loss).card < (relabelColors e support).card := by
        simpa only [relabelColors_card] using hcard
      have hf := hmin (relabelColors e loss) hsubW hcardW
      rw [← relabelColors_sdiff] at hf
      exact (IsForcing_relabel_iff e adjV adjW hadj _).mp hf
  · rintro ⟨hsub, hfail, hmin⟩
    refine ⟨(relabelColors_subset_iff e _ _).mpr hsub, ?_, ?_⟩
    · intro hf
      apply hfail
      rw [← relabelColors_sdiff] at hf
      exact (IsForcing_relabel_iff e adjV adjW hadj _).mp hf
    · intro lossW hloss hcard
      let lossV := relabelColors e.symm lossW
      have hmap : relabelColors e lossV = lossW := by simp [lossV]
      have hsubV : lossV ⊆ blue := by
        apply (relabelColors_subset_iff e _ _).mp
        simpa only [hmap] using hloss
      have hcardV : lossV.card < support.card := by
        simpa only [lossV, relabelColors_card] using hcard
      have hf := hmin lossV hsubV hcardV
      rw [← hmap, ← relabelColors_sdiff]
      exact (IsForcing_relabel_iff e adjV adjW hadj _).mpr hf

theorem RobustBy_relabel_iff (e : V ≃ W)
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (hadj : ∀ x y, adjW (e x) (e y) ↔ adjV x y)
    (blue allowed : Finset V) (budget deadline : ℕ) :
    RobustBy adjW (relabelColors e blue) (relabelColors e allowed) budget deadline ↔
      RobustBy adjV blue allowed budget deadline := by
  constructor
  · intro h loss hsub hcard
    have hsubW := (relabelColors_subset_iff e _ _).mpr hsub
    have hcardW : (relabelColors e loss).card ≤ budget := by
      simpa only [relabelColors_card] using hcard
    have hf := h (relabelColors e loss) hsubW hcardW
    rw [← relabelColors_sdiff] at hf
    exact (FinishesBy_relabel_iff e adjV adjW hadj _ deadline).mp hf
  · intro h lossW hsub hcard
    let lossV := relabelColors e.symm lossW
    have hmap : relabelColors e lossV = lossW := by simp [lossV]
    have hsubV : lossV ⊆ allowed := by
      apply (relabelColors_subset_iff e _ _).mp
      simpa only [hmap] using hsub
    have hcardV : lossV.card ≤ budget := by
      simpa only [lossV, relabelColors_card] using hcard
    have hf := h lossV hsubV hcardV
    rw [← hmap, ← relabelColors_sdiff]
    exact (FinishesBy_relabel_iff e adjV adjW hadj _ deadline).mpr hf

theorem EveryMinimumSupport_transfer (e : V ≃ W)
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (hadj : ∀ x y, adjW (e x) (e y) ↔ adjV x y)
    (hV : EveryMinimumSupport adjV) : EveryMinimumSupport adjW := by
  intro blueW hforcing supportW hminimum budget deadline
  let blueV := relabelColors e.symm blueW
  let supportV := relabelColors e.symm supportW
  have hb : relabelColors e blueV = blueW := by simp [blueV]
  have hh : relabelColors e supportV = supportW := by simp [supportV]
  have hfV : IsForcing adjV blueV :=
    (IsForcing_relabel_iff e adjV adjW hadj blueV).mp (by simpa only [hb] using hforcing)
  have hmV : IsMinimumKilling adjV blueV supportV :=
    (IsMinimumKilling_relabel_iff e adjV adjW hadj blueV supportV).mp
      (by simpa only [hb, hh] using hminimum)
  have h := hV blueV hfV supportV hmV budget deadline
  have hmap := (RobustBy_relabel_iff e adjV adjW hadj blueV blueV budget deadline).trans
    (h.trans (RobustBy_relabel_iff e adjV adjW hadj blueV supportV budget deadline).symm)
  simpa only [hb, hh] using hmap

theorem EveryMinimumSupport_relabel_iff (e : V ≃ W)
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (hadj : ∀ x y, adjW (e x) (e y) ↔ adjV x y) :
    EveryMinimumSupport adjW ↔ EveryMinimumSupport adjV := by
  have hsymm : ∀ x y, adjV (e.symm x) (e.symm y) ↔ adjW x y := by
    intro x y
    simpa only [Equiv.apply_symm_apply] using (hadj (e.symm x) (e.symm y)).symm
  exact ⟨EveryMinimumSupport_transfer e.symm adjW adjV hsymm,
    EveryMinimumSupport_transfer e adjV adjW hadj⟩

theorem completionTime_relabel (e : V ≃ W)
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (hadj : ∀ x y, adjW (e x) (e y) ↔ adjV x y) (blue : Finset V) :
    completionTime adjW (relabelColors e blue) = completionTime adjV blue := by
  apply (enat_eq_iff_finite_deadlines _ _).mpr
  intro t
  rw [completionTime_le_iff, completionTime_le_iff, FinishesBy_relabel_iff e adjV adjW hadj]

theorem worstTime_relabel (e : V ≃ W)
    (adjV : V → V → Prop) (adjW : W → W → Prop)
    (hadj : ∀ x y, adjW (e x) (e y) ↔ adjV x y)
    (blue allowed : Finset V) (budget : ℕ) :
    worstTime adjW (relabelColors e blue) (relabelColors e allowed) budget =
      worstTime adjV blue allowed budget := by
  apply (enat_eq_iff_finite_deadlines _ _).mpr
  intro t
  rw [worstTime_le_iff, worstTime_le_iff, RobustBy_relabel_iff e adjV adjW hadj]

theorem EveryMinimumSupport_iso_iff (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G ≃g H) : EveryMinimumSupport G.Adj ↔ EveryMinimumSupport H.Adj := by
  exact (EveryMinimumSupport_relabel_iff e.toEquiv G.Adj H.Adj
    (fun _ _ => e.map_adj_iff)).symm

end FaultObservationResearch
