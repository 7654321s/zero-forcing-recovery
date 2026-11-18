module

public import FiniteWitness

@[expose] public section

set_option autoImplicit false

namespace FaultObservationResearch.MaskForcing

variable {n : ℕ}

def tableNeighbors (rows : Array (List (Fin n))) : Neighbors n :=
  fun x => rows[x.val]?.getD []

def edgeTest (edges : List (ℕ × ℕ)) (a b : ℕ) : Bool :=
  edges.contains (a, b) || edges.contains (b, a)

def edgeTable (n : ℕ) (edges : List (ℕ × ℕ)) : Array (List (Fin n)) :=
  Array.ofFn (fun a : Fin n => (List.finRange n).filter (fun b => edgeTest edges a.val b.val))

def pairPresent (rows : Array (List (Fin n))) (edge : ℕ × ℕ) : Bool :=
  let (a, b) := edge
  if ha : a < n then
    if hb : b < n then
      (tableNeighbors rows ⟨a, ha⟩).contains ⟨b, hb⟩ &&
        (tableNeighbors rows ⟨b, hb⟩).contains ⟨a, ha⟩
    else false
  else false

def tableMatches (rows : Array (List (Fin n))) (edges : List (ℕ × ℕ)) : Bool :=
  (rows.size == n) &&
  (List.finRange n).all (fun a =>
    let row := tableNeighbors rows a
    decide row.Nodup && row.all (fun b => edgeTest edges a.val b.val)) &&
  edges.all (pairPresent rows)

theorem tableMatches_distinct (rows : Array (List (Fin n))) (edges : List (ℕ × ℕ))
    (hMatch : tableMatches rows edges) (a : Fin n) : (tableNeighbors rows a).Nodup := by
  simp only [tableMatches, Bool.and_eq_true, and_assoc] at hMatch
  have hRow := List.all_eq_true.mp hMatch.2.1 a (List.mem_finRange a)
  simp only [Bool.and_eq_true] at hRow
  exact of_decide_eq_true hRow.1

theorem edgeTable_adj (edges : List (ℕ × ℕ)) (a b : Fin n) :
    adj (tableNeighbors (edgeTable n edges)) a b ↔
      (a.val, b.val) ∈ edges ∨ (b.val, a.val) ∈ edges := by
  have h : a.val < (edgeTable n edges).size := by simp [edgeTable]
  rw [adj, tableNeighbors, getElem?_pos (edgeTable n edges) a.val h]
  simp [edgeTable, edgeTest, Bool.or_eq_true]

theorem edgeTable_distinct (edges : List (ℕ × ℕ)) (a : Fin n) :
    (tableNeighbors (edgeTable n edges) a).Nodup := by
  have h : a.val < (edgeTable n edges).size := by simp [edgeTable]
  rw [tableNeighbors, getElem?_pos (edgeTable n edges) a.val h]
  simpa [edgeTable] using (List.nodup_finRange n).filter (fun b => edgeTest edges a.val b.val)

theorem tableMatches_adj (rows : Array (List (Fin n))) (edges : List (ℕ × ℕ))
    (hMatch : tableMatches rows edges) :
    adj (tableNeighbors rows) = adj (tableNeighbors (edgeTable n edges)) := by
  funext a b
  apply propext
  rw [edgeTable_adj]
  simp only [tableMatches, Bool.and_eq_true, and_assoc] at hMatch
  constructor
  · intro h
    have hRow := List.all_eq_true.mp hMatch.2.1 a (List.mem_finRange a)
    simp only [Bool.and_eq_true] at hRow
    have hb := List.all_eq_true.mp hRow.2 b h
    simpa [edgeTest, Bool.or_eq_true] using hb
  · intro h
    rcases h with hab | hba
    · have hp := List.all_eq_true.mp hMatch.2.2 (a.val, b.val) hab
      simp only [pairPresent, dite_true, a.isLt, b.isLt, Bool.and_eq_true,
        List.contains_iff_mem] at hp
      exact hp.1
    · have hp := List.all_eq_true.mp hMatch.2.2 (b.val, a.val) hba
      simp only [pairPresent, dite_true, a.isLt, b.isLt, Bool.and_eq_true,
        List.contains_iff_mem] at hp
      exact hp.2

theorem check_numbered_witness (edges : List (ℕ × ℕ)) (rows : Array (List (Fin n)))
    (w : Witness n) (sameGraph : tableMatches rows edges) (valid : w.check (tableNeighbors rows)) :
    BudgetOnePairWitness (adj (tableNeighbors (edgeTable n edges)))
      (colors n w.blue) w.support w.slow w.early := by
  rw [← tableMatches_adj rows edges sameGraph]
  exact w.checked_sound _ (tableMatches_distinct rows edges sameGraph) valid

def cycleEdges (order : ℕ) : List (ℕ × ℕ) :=
  (List.range order).map (fun x => (x, (x + 1) % order))

/-- Introduce length consecutive vertices beginning at start, and join
them as a path beginning at the retained root. -/
def pendantEdges (root start length : ℕ) : List (ℕ × ℕ) :=
  (List.range length).map fun i => (if i == 0 then root else start + i - 1, start + i)

end FaultObservationResearch.MaskForcing

#print axioms FaultObservationResearch.MaskForcing.edgeTable_adj
#print axioms FaultObservationResearch.MaskForcing.check_numbered_witness
