import YangMills.Construction.SummableBoundsOfTheFlow.AGapAmongFinitelyManyPoints
import Mathlib
set_option autoImplicit false
open Finset
namespace YangMills.Construction.FiniteMetricGap
theorem existsGapAmongFinitePoints_holds : ExistsGapAmongFinitePoints := by
  intro M P d Z i₀ j₀ hM hself hsymm htri
  have hnn : ∀ z z', 0 ≤ d z z' := by
    intro z z'
    have h := htri z z' z
    rw [hself, hsymm z' z] at h
    linarith
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  set l : ℝ := d (Z i₀) (Z j₀) / ((M : ℝ) - 1) with hl
  by_cases hl0 : l ≤ 0
  · have h0 : 0 < M := by omega
    have h1 : 1 < M := by omega
    refine ⟨{⟨0, h0⟩}, ⟨_, mem_singleton_self _⟩, ⟨⟨1, h1⟩, ?_⟩, ?_⟩
    · simp [Fin.ext_iff]
    · intro i _ j _
      exact hl0.trans (hnn _ _)
  have hlpos : 0 < l := not_le.mp hl0
  have hD : d (Z i₀) (Z j₀) = ((M : ℝ) - 1) * l := by
    rw [hl]
    field_simp
  have hne : i₀ ≠ j₀ := by
    intro h
    rw [h, hself] at hD
    have := mul_pos hM1 hlpos
    linarith
  set r : Fin M → ℝ := fun i => d (Z i₀) (Z i) with hr
  have hgap : ∃ k : Fin (M - 1), ∀ i, ¬ (((k : ℕ) : ℝ) * l < r i ∧ r i < (((k : ℕ) : ℝ) + 1) * l) := by
    by_contra hcon
    push_neg at hcon
    choose pt hpt using hcon
    have hinj : Function.Injective pt := by
      intro k k' hk
      by_contra hne'
      have hlt : (k : ℕ) < k' ∨ (k' : ℕ) < k := by
        rcases Nat.lt_trichotomy k k' with h | h | h
        · exact Or.inl h
        · exact absurd (Fin.ext h) hne'
        · exact Or.inr h
      have a1 := (hpt k).1
      have a2 := (hpt k).2
      have b1 := (hpt k').1
      have b2 := (hpt k').2
      rw [hk] at a1 a2
      rcases hlt with h | h
      · have : ((k : ℕ) : ℝ) + 1 ≤ ((k' : ℕ) : ℝ) := by exact_mod_cast h
        have := mul_le_mul_of_nonneg_right this hlpos.le
        linarith
      · have : ((k' : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast h
        have := mul_le_mul_of_nonneg_right this hlpos.le
        linarith
    have hav : ∀ k, pt k ∈ (univ.erase i₀).erase j₀ := by
      intro k
      have a1 := (hpt k).1
      have a2 := (hpt k).2
      have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
      have hkM : ((k : ℕ) : ℝ) + 1 ≤ (M : ℝ) - 1 := by
        have h := k.2
        have : (k : ℕ) + 1 ≤ M - 1 := h
        have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast this
        rw [Nat.cast_sub (by omega)] at h2
        push_cast at h2
        exact h2
      simp only [mem_erase, mem_univ, and_true]
      constructor
      · intro h
        rw [h] at a2
        simp only [hr] at a2
        have := mul_le_mul_of_nonneg_right hkM hlpos.le
        rw [hD] at a2
        linarith
      · intro h
        rw [h] at a1
        simp only [hr, hself] at a1
        have := mul_nonneg hk0 hlpos.le
        linarith
    have hcard : (univ : Finset (Fin (M - 1))).card ≤ ((univ.erase i₀).erase j₀).card :=
      card_le_card_of_injOn pt (fun k _ => hav k) hinj.injOn
    have hc2 : ((univ.erase i₀).erase j₀).card = M - 2 := by
      rw [card_erase_of_mem (by simp [hne.symm]), card_erase_of_mem (mem_univ _)]
      simp
      omega
    rw [hc2, card_univ, Fintype.card_fin] at hcard
    omega
  obtain ⟨k, hk⟩ := hgap
  refine ⟨univ.filter fun i => r i ≤ ((k : ℕ) : ℝ) * l, ⟨i₀, ?_⟩, ⟨j₀, ?_⟩, ?_⟩
  · simp only [mem_filter, mem_univ, true_and, hr, hself]
    exact mul_nonneg (Nat.cast_nonneg _) hlpos.le
  · have hkM : ((k : ℕ) : ℝ) + 1 ≤ (M : ℝ) - 1 := by
      have : (k : ℕ) + 1 ≤ M - 1 := k.2
      have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h2
      push_cast at h2
      exact h2
    simp only [mem_compl, mem_filter, mem_univ, true_and, not_le, hr]
    rw [hD]
    have := mul_le_mul_of_nonneg_right hkM hlpos.le
    nlinarith
  · intro i hi j hj
    have hi' : r i ≤ ((k : ℕ) : ℝ) * l := (mem_filter.mp hi).2
    have hj' : ((k : ℕ) : ℝ) * l < r j := by
      simpa using hj
    have hj2 : (((k : ℕ) : ℝ) + 1) * l ≤ r j := by
      by_contra h
      exact hk j ⟨hj', not_le.mp h⟩
    have ht := htri (Z i₀) (Z i) (Z j)
    have e1 : r i = d (Z i₀) (Z i) := rfl
    have e2 : r j = d (Z i₀) (Z j) := rfl
    nlinarith
end YangMills.Construction.FiniteMetricGap
