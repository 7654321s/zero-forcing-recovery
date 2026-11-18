module

/- Transport the checked strict time-gap obstruction to original terminal path pairs. -/
public import «formalization-tree-two-center-realization»
public import «formalization-tree-attachments»
public import «formalization-two-center-equal-nonadjacent»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u
variable {V : Type u}

theorem terminal_pairs_strict_not_support [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (a b : V) (hab : a ≠ b)
    (P : TerminalTreeCutPair G a b hab) (Q : TerminalTreeCutPair G b a hab.symm)
    (hstrict : max (Nat.card P.first) (Nat.card P.second) + 1 <
      Nat.card Q.first + Nat.card Q.second) : ¬ EveryMinimumSupport G.Adj := by
  classical
  obtain ⟨W, R, x, y, m, n, k, l, hW, hR, hxy, ⟨e⟩, _, hm, hn, hk, hl⟩ :=
    terminal_pairs_two_center_realization G hG a b hab P Q
  let : Finite W := hW
  let : Fintype W := Fintype.ofFinite W
  have hgap : max (k + 1) (l + 1) < m + n + 1 := by
    rw [← hm, ← hn, ← hk, ← hl] at hstrict
    omega
  have hbad := (twoCenter_strict_tree_witness R hR x y hxy.symm m n k l hgap).2
  intro hsupport
  exact hbad ((EveryMinimumSupport_iso_iff (twoCenterGraph R x y m n k l) G e).mpr hsupport)

theorem terminal_pairs_equal_nonadjacent_not_support [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (a b : V) (hab : a ≠ b)
    (P : TerminalTreeCutPair G a b hab) (Q : TerminalTreeCutPair G b a hab.symm)
    (n : ℕ) (hQlong : Nat.card Q.first = n + 1) (hQshort : Nat.card Q.second = 1)
    (hPlong : Nat.card P.first = n + 1) (hPshort : Nat.card P.second = 1)
    (hnadj : ¬ G.Adj a b) : ¬ EveryMinimumSupport G.Adj := by
  classical
  obtain ⟨W, R, x, y, hW, hR, hxy, ⟨e⟩, hadj⟩ :=
    terminal_pairs_prescribed_two_center_realization G hG a b hab P Q n 0 n 0
      hQlong hQshort hPlong hPshort
  let : Finite W := hW
  let : Fintype W := Fintype.ofFinite W
  have hnR : ¬ R.Adj x y := fun h => hnadj (hadj.mp h).symm
  have hbad := (equal_nonadjacent_tree_not_support R hR x y hxy.symm n hnR).2
  intro hsupport
  exact hbad ((EveryMinimumSupport_iso_iff (twoCenterGraph R x y n 0 n 0) G e).mpr hsupport)

end FaultObservationResearch
