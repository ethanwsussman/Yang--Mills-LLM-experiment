import YangMills.Construction.DirichletOperator.SidesOfTheBlocksAtALevel
import YangMills.Construction.Torus.ChainScales
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus
namespace PartitionCubes.LevelCubeSides
theorem eq_of_addCircle_coe_eq_of_abs_lt {S a b : ℝ} (hS : 0 < S) (hab : |a - b| < S)
    (h : (a : AddCircle S) = (b : AddCircle S)) : a = b := by
  have h0 : ((a - b : ℝ) : AddCircle S) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  rw [← hk, zsmul_eq_mul, abs_mul, abs_of_pos hS] at hab
  have h1 : |(k : ℝ)| < 1 := by
    by_contra hge
    exact absurd hab (not_lt.mpr (le_mul_of_one_le_left hS.le (not_lt.mp hge)))
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast h1)
  rw [hk0, zero_smul] at hk
  exact sub_eq_zero.mp hk.symm
theorem statement_holds (hScales : ChainScales.ScalesStatement) : Statement := by
  intro 𝒮 K m M R₁ h n hn
  have hL : 2 ≤ 𝒮.L := le_trans (by norm_num) 𝒮.thirteen_le_L
  obtain ⟨u, -, hM, hmul⟩ :=
    (hScales 4 𝒮.L 𝒮.side 𝒮.ξ M R₁ 𝒮.s 𝒮.Ω hL h.separated).side_even_multiple
  have hn' : (n : ℤ) ≤ (lastNonemptyIndex 𝒮.Ω : ℤ) := Int.ofNat_le.mpr hn
  obtain ⟨k, hk, hS⟩ := hmul ((n : ℤ) + (u : ℤ)) (by omega)
  have hLpos : (0 : ℝ) < (𝒮.L : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcube : scaleSpacing 𝒮.L 𝒮.ξ ((n : ℤ) + (u : ℤ)) = cubeSide 𝒮 M n := by
    simp only [cubeSide, RegionSequence.NestedRegions.scale, scaleSpacing]
    rw [hM, zpow_add₀ hLpos.ne']
    simp only [zpow_natCast, Nat.cast_pow]
    ring
  rw [hcube] at hS
  have hb : 0 < cubeSide 𝒮 M n := by
    rw [← hcube]
    exact mul_pos (zpow_pos hLpos _) 𝒮.ξ_pos
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
  have hle : 2 * cubeSide 𝒮 M n ≤ 𝒮.side := by
    rw [hS, mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hb.le hk1) (by norm_num)
  refine ⟨⟨(k : ℤ), ?_⟩, hle, ?_⟩
  · rw [hS, Int.cast_natCast, mul_div_assoc, div_self hb.ne', mul_one]
  · intro c p hp q hq hpq
    funext μ
    have hμ : ((p μ : ℝ) : AddCircle 𝒮.side) = (q μ : AddCircle 𝒮.side) := congrFun hpq μ
    refine eq_of_addCircle_coe_eq_of_abs_lt 𝒮.side_pos ?_ hμ
    have h₁ := abs_lt.mp (hp μ)
    have h₂ := abs_lt.mp (hq μ)
    rw [abs_lt]
    constructor <;> linarith only [h₁.1, h₁.2, h₂.1, h₂.2, hle]
end PartitionCubes.LevelCubeSides
end YangMills.Construction
end
