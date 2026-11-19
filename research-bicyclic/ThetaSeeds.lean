import «formalization-finite-check»
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false

namespace FaultObservationResearch

/-- Vertices `0` and `1` are the common endpoints. Number the internal
vertices of each path in order from `0` to `1`. -/
def thetaAdj {n : ℕ} (rows : List ℕ) (v w : Fin n) : Prop :=
  Nat.testBit (rows[v.val]?.getD 0) w.val = true

instance {n : ℕ} (rows : List ℕ) : DecidableRel (thetaAdj (n := n) rows) := by
  intro v w
  unfold thetaAdj
  infer_instance

set_option maxRecDepth 32768
set_option maxHeartbeats 64000000

theorem theta122_every_minimum_support : EveryMinimumSupport (thetaAdj (n := 4) [14, 13, 3, 3]) :=
  (computedEveryMinimumSupport_iff _).mp (by decide +kernel)

theorem theta222_every_minimum_support : EveryMinimumSupport (thetaAdj (n := 5) [28, 28, 3, 3, 3]) :=
  (computedEveryMinimumSupport_iff _).mp (by decide +kernel)

theorem theta223_every_minimum_support : EveryMinimumSupport (thetaAdj (n := 6) [28, 44, 3, 3, 33, 18]) :=
  (computedEveryMinimumSupport_iff _).mp (by
    intro blue
    fin_cases blue <;> decide +kernel)

end FaultObservationResearch

#print axioms FaultObservationResearch.theta122_every_minimum_support
#print axioms FaultObservationResearch.theta222_every_minimum_support
#print axioms FaultObservationResearch.theta223_every_minimum_support
