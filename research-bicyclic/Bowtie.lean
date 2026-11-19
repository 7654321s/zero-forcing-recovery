import «formalization-finite-check»

set_option autoImplicit false

namespace FaultObservationResearch

/-- The two triangles are `0, 1, 2` and `0, 3, 4`. -/
def bowtieAdj (v w : Fin 5) : Prop :=
  v ≠ w ∧ (v.val = 0 ∨ w.val = 0 ∨ (v.val + 1) / 2 = (w.val + 1) / 2)

instance : DecidableRel bowtieAdj := by
  intro v w
  unfold bowtieAdj
  infer_instance

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem bowtie_computed_support : computedEveryMinimumSupport bowtieAdj := by
  decide +kernel

theorem bowtie_every_minimum_support : EveryMinimumSupport bowtieAdj :=
  (computedEveryMinimumSupport_iff bowtieAdj).mp bowtie_computed_support

end FaultObservationResearch

#print axioms FaultObservationResearch.bowtie_every_minimum_support
