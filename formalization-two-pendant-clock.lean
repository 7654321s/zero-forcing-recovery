module

/-
Original-graph clock for two interacting pendant arms. Ordinary path propagation
and this local clock are tools, not a claim of research priority. The full-tree
support-time classification remains unproved.
-/
public import «formalization-two-pendant-model»
public import «formalization-path-reversal-tools»

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace FaultObservationResearch
universe u

theorem path_zero_finishes_n (n : ℕ) :
    FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj {0} n := by
  classical
  have hc : (PathIntervalWhites n {0} 0 (Fin.last n)).card ≤ n := by
    calc
      _ ≤ (Finset.univ.erase (0 : Fin (n + 1))).card := by
        apply Finset.card_le_card
        intro x hx
        have hn := (Finset.mem_filter.mp hx).2.2.2
        simpa only [Finset.mem_erase, Finset.mem_univ, and_true,
          Finset.mem_singleton] using hn
      _ = n := by simp
  apply Finset.eq_univ_of_forall
  intro x
  apply path_interval_left_sided_upper n {0} 0 (Fin.last n) ?_ n hc x
    (Nat.zero_le _) (by have := x.isLt; change x.val ≤ n; omega)
  constructor
  · exact Finset.mem_singleton_self _
  · intro y _ hy
    change y.val < 0 at hy
    omega

theorem path_last_finishes_n (n : ℕ) :
    FinishesBy (SimpleGraph.pathGraph (n + 1)).Adj {Fin.last n} n := by
  classical
  have hc : (PathIntervalWhites n {Fin.last n} 0 (Fin.last n)).card ≤ n := by
    calc
      _ ≤ (Finset.univ.erase (Fin.last n)).card := by
        apply Finset.card_le_card
        intro x hx
        have hn := (Finset.mem_filter.mp hx).2.2.2
        simpa only [Finset.mem_erase, Finset.mem_univ, and_true,
          Finset.mem_singleton] using hn
      _ = n := by simp
  apply Finset.eq_univ_of_forall
  intro x
  apply path_interval_one_sided_upper n {Fin.last n} 0 (Fin.last n) ?_ n hc x
    (Nat.zero_le _) (by have := x.isLt; change x.val ≤ n; omega)
  constructor
  · exact Finset.mem_singleton_self _
  · intro y _ hy
    change n < y.val at hy
    have := y.isLt
    omega

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem twoPendant_armA_by_path_deadline (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b)) (seed : Finset (Fin (a + 1))) (t : ℕ)
    (hr : twoPendantCore V a b root ∈ C)
    (hinitial : ∀ i ∈ seed, twoPendantA V a b i ∈ C)
    (hfinish : FinishesBy (SimpleGraph.pathGraph (a + 1)).Adj seed t) :
    ∀ i, twoPendantA V a b i ∈ colorAfter (twoPendantGraph R root a b).Adj C t := by
  classical
  intro i
  refine colorAfter_embeds_with_blue_exterior (SimpleGraph.pathGraph (a + 1))
    (twoPendantGraph R root a b) (twoPendantA V a b) (fun h => h) seed C
    ?_ hinitial t i ?_
  · intro j z hz
    rcases z with x | (k | l)
    · change x = root ∧ j = 0 at hz
      rcases hz with ⟨rfl, _⟩
      exact Or.inr hr
    · exact Or.inl ⟨k, rfl, hz⟩
    · exact hz.elim
  · rw [hfinish]
    exact Finset.mem_univ _

theorem twoPendant_armB_by_path_deadline (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b)) (seed : Finset (Fin (b + 1))) (t : ℕ)
    (hr : twoPendantCore V a b root ∈ C)
    (hinitial : ∀ i ∈ seed, twoPendantB V a b i ∈ C)
    (hfinish : FinishesBy (SimpleGraph.pathGraph (b + 1)).Adj seed t) :
    ∀ i, twoPendantB V a b i ∈ colorAfter (twoPendantGraph R root a b).Adj C t := by
  classical
  intro i
  refine colorAfter_embeds_with_blue_exterior (SimpleGraph.pathGraph (b + 1))
    (twoPendantGraph R root a b) (twoPendantB V a b) (fun h => h) seed C
    ?_ hinitial t i ?_
  · intro j z hz
    rcases z with x | (k | l)
    · change x = root ∧ j = 0 at hz
      rcases hz with ⟨rfl, _⟩
      exact Or.inr hr
    · exact hz.elim
    · exact Or.inl ⟨l, rfl, hz⟩
  · rw [hfinish]
    exact Finset.mem_univ _

theorem twoPendant_delayed_arm_speed_limits (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hA : ∀ i, twoPendantA V a b i ∉ C)
    (hB : ∀ j, twoPendantB V a b j ∈ C → b ≤ j.val) (t : ℕ) :
    (∀ i, twoPendantA V a b i ∈ colorAfter (twoPendantGraph R root a b).Adj C t →
      b + i.val + 1 ≤ t) ∧
    (∀ j, twoPendantB V a b j ∈ colorAfter (twoPendantGraph R root a b).Adj C t →
      b ≤ j.val + t) := by
  classical
  let G := twoPendantGraph R root a b
  induction t with
  | zero =>
    constructor
    · intro i hi; exact False.elim (hA i hi)
    · intro j hj; simpa only [Nat.add_zero] using hB j hj
  | succ t ih =>
    constructor
    · intro i hi
      rcases (mem_synchronousStep G.Adj (colorAfter G.Adj C t) _).mp hi with
        hold | ⟨source, hs, ha, hu⟩
      · have := ih.1 i hold
        omega
      · rcases source with x | (j | k)
        · change x = root ∧ i = 0 at ha
          rcases ha with ⟨rfl, rfl⟩
          have hhead : twoPendantB V a b 0 ∈ colorAfter G.Adj C t := by
            by_contra hwhite
            have heq := hu (twoPendantB V a b 0) ⟨rfl, rfl⟩ hwhite
            cases heq
          have hb := ih.2 0 hhead
          change b ≤ 0 + t at hb
          change b + 0 + 1 ≤ t + 1
          omega
        · have hb := ih.1 j hs
          rcases SimpleGraph.pathGraph_adj.mp ha with hadj | hadj <;> omega
        · exact ha.elim
    · intro i hi
      rcases (mem_synchronousStep G.Adj (colorAfter G.Adj C t) _).mp hi with
        hold | ⟨source, hs, ha, hu⟩
      · have := ih.2 i hold
        omega
      · rcases source with x | (j | k)
        · change x = root ∧ i = 0 at ha
          rcases ha with ⟨rfl, rfl⟩
          have hhead : twoPendantA V a b 0 ∈ colorAfter G.Adj C t := by
            by_contra hwhite
            have heq := hu (twoPendantA V a b 0) ⟨rfl, rfl⟩ hwhite
            cases heq
          have hb := ih.1 0 hhead
          change b + 0 + 1 ≤ t at hb
          change b ≤ 0 + (t + 1)
          omega
        · exact ha.elim
        · have hb := ih.2 k hs
          rcases SimpleGraph.pathGraph_adj.mp ha with hadj | hadj <;> omega

theorem twoPendant_delayed_completion_lower (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hA : ∀ i, twoPendantA V a b i ∉ C)
    (hB : ∀ j, twoPendantB V a b j ∈ C → b ≤ j.val)
    (t : ℕ) (hfinish : FinishesBy (twoPendantGraph R root a b).Adj C t) :
    a + b + 1 ≤ t := by
  have hm : twoPendantA V a b (Fin.last a) ∈
      colorAfter (twoPendantGraph R root a b).Adj C t := by
    rw [hfinish]
    exact Finset.mem_univ _
  have hb := (twoPendant_delayed_arm_speed_limits R root a b C hA hB t).1 _ hm
  change b + a + 1 ≤ t at hb
  omega

theorem twoPendant_finish_of_core_and_B_last (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hcore : ∀ x, twoPendantCore V a b x ∈ C)
    (hB : twoPendantB V a b (Fin.last b) ∈ C) :
    FinishesBy (twoPendantGraph R root a b).Adj C (a + b + 1) := by
  classical
  let G := twoPendantGraph R root a b
  have hBfill := twoPendant_armB_by_path_deadline R root a b C {Fin.last b} b
    (hcore root) (by
      intro j hj
      have heq := Finset.mem_singleton.mp hj
      simpa only [heq] using hB) (path_last_finishes_n b)
  have hcoreAt : ∀ x, twoPendantCore V a b x ∈ colorAfter G.Adj C b :=
    fun x => colorAfter_mono_time G.Adj C (Nat.zero_le _) (hcore x)
  have hheads := twoPendant_heads_in_step R root a b (colorAfter G.Adj C b)
    hcoreAt (Or.inr (hBfill 0))
  have hAfill := twoPendant_armA_by_path_deadline R root a b
    (colorAfter G.Adj C (b + 1)) {0} a
    (colorAfter_mono_time G.Adj C (Nat.zero_le _) (hcore root)) (by
      intro i hi
      have heq := Finset.mem_singleton.mp hi
      subst i
      exact hheads.1) (path_zero_finishes_n a)
  apply Finset.eq_univ_of_forall
  rintro (x | (i | j))
  · exact colorAfter_mono_time G.Adj C (Nat.zero_le _) (hcore x)
  · have heq : a + b + 1 = (b + 1) + a := by omega
    rw [heq, colorAfter_add]
    exact hAfill i
  · exact colorAfter_mono_time G.Adj C (by omega : b ≤ a + b + 1) (hBfill j)

theorem twoPendant_delayed_completion_iff (R : SimpleGraph V) (root : V) (a b : ℕ)
    (C : Finset (TwoPendantVertex V a b))
    (hcore : ∀ x, twoPendantCore V a b x ∈ C)
    (hA : ∀ i, twoPendantA V a b i ∉ C)
    (hB : ∀ j, twoPendantB V a b j ∈ C ↔ j = Fin.last b) (t : ℕ) :
    FinishesBy (twoPendantGraph R root a b).Adj C t ↔ a + b + 1 ≤ t := by
  constructor
  · apply twoPendant_delayed_completion_lower R root a b C hA
    intro j hj
    have heq := (hB j).mp hj
    subst j
    exact le_rfl
  · intro ht
    exact FinishesBy_mono_time _ C
      (twoPendant_finish_of_core_and_B_last R root a b C hcore ((hB _).mpr rfl)) ht

end FaultObservationResearch
