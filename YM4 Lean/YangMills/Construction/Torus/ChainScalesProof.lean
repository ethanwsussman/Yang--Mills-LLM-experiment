import YangMills.Construction.Torus.ChainScales
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
namespace YangMills.Construction.Torus.ChainScales
theorem scalesStatement_holds : ScalesStatement := by
  intro d L S ξ M R₁ t Ω hL h
  have hL0 : (L : ℝ) ≠ 0 := by
    have : 0 < L := by omega
    positivity
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ L)
  have hξ := h.scale_pos
  have hbdd : BddAbove {n | (Ω n).Nonempty} := by
    refine ⟨t, fun n hn => ?_⟩
    by_contra hlt
    exact (Set.not_nonempty_iff_eq_empty.mpr (h.eq_empty_of_lt n (not_le.mp hlt))) hn
  have hne : {n | (Ω n).Nonempty}.Nonempty := ⟨0, h.zero_nonempty⟩
  have hlast : (Ω (lastNonemptyIndex Ω)).Nonempty := Nat.sSup_mem hne hbdd
  have hle : ∀ n, (Ω n).Nonempty → n ≤ lastNonemptyIndex Ω := fun n hn => le_csSup hbdd hn
  have hlastle : lastNonemptyIndex Ω ≤ t := by
    by_contra hlt
    exact (Set.not_nonempty_iff_eq_empty.mpr (h.eq_empty_of_lt _ (not_le.mp hlt))) hlast
  obtain ⟨hLM, μ, hμ⟩ := h.blockSize_isPowerGe
  obtain ⟨k, hk, hS⟩ := h.period_eq_even_mul
  have hμ1 : 1 ≤ μ := by
    rcases Nat.eq_zero_or_pos μ with h0 | h0
    · subst h0
      simp only [pow_zero] at hμ
      omega
    · exact h0
  refine ⟨hlastle, hlast, ?_, ?_, ⟨μ, hμ1, hμ, ?_⟩, ?_⟩
  · intro n hn
    by_contra hne'
    exact absurd (hle n (Set.nonempty_iff_ne_empty.mpr hne')) (not_le.mpr hn)
  · intro n
    rcases lt_or_ge n t with hn | hn
    · exact h.succ_subset n hn
    · rw [h.eq_empty_of_lt (n + 1) (by omega)]
      exact Set.empty_subset _
  · intro i hi
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (lastNonemptyIndex Ω : ℤ) + (μ : ℤ) = i + (j : ℤ) :=
      ⟨((lastNonemptyIndex Ω : ℤ) + (μ : ℤ) - i).toNat, by omega⟩
    refine ⟨k * L ^ j, by positivity, ?_⟩
    have hpow : (M : ℝ) * (L : ℝ) ^ (lastNonemptyIndex Ω : ℤ) = (L : ℝ) ^ j * (L : ℝ) ^ i := by
      rw [hμ, Nat.cast_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hL0, ← zpow_add₀ hL0]
      congr 1
      omega
    rw [hS]
    simp only [scaleSpacing]
    push_cast
    calc 2 * (k : ℝ) * ((M : ℝ) * ((L : ℝ) ^ (lastNonemptyIndex Ω : ℤ) * ξ))
        = 2 * (k : ℝ) * (((M : ℝ) * (L : ℝ) ^ (lastNonemptyIndex Ω : ℤ)) * ξ) := by ring
      _ = 2 * ((k : ℝ) * (L : ℝ) ^ j) * ((L : ℝ) ^ i * ξ) := by rw [hpow]; ring
  · intro n hn
    have hnt : (n : ℤ) ≤ (lastNonemptyIndex Ω : ℤ) := by exact_mod_cast hle n hn
    have hsp : scaleSpacing L ξ n ≤ scaleSpacing L ξ (lastNonemptyIndex Ω) := by
      simp only [scaleSpacing]
      exact mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ hL1 hnt) hξ.le
    have hsp0 : 0 ≤ scaleSpacing L ξ (lastNonemptyIndex Ω) := by
      simp only [scaleSpacing]
      positivity
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    rw [hS]
    calc 2 * (M : ℝ) * scaleSpacing L ξ n
        ≤ 2 * (M : ℝ) * scaleSpacing L ξ (lastNonemptyIndex Ω) :=
          mul_le_mul_of_nonneg_left hsp (by positivity)
      _ = 2 * 1 * ((M : ℝ) * scaleSpacing L ξ (lastNonemptyIndex Ω)) := by ring
      _ ≤ 2 * (k : ℝ) * ((M : ℝ) * scaleSpacing L ξ (lastNonemptyIndex Ω)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hM0 hsp0)
          linarith
end YangMills.Construction.Torus.ChainScales
