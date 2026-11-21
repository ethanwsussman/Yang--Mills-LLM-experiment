import YangMills.Construction.HolomorphicExtension.HullConstantsBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HolomorphicExtension
theorem hullConstantsBounds : HullConstantsBoundsStatement := by
  intro ε hε hε1 w L q t
  have hpi : 0 < Real.pi := Real.pi_pos
  have hhalf : 0 < 1 - ε / 2 := by linarith
  have h24 : 0 < 1 - ε / 24 := by linarith
  have hw : 0 < w := mul_pos hhalf (by linarith)
  have hw2 : w < Real.pi / 2 := by
    have : w = Real.pi / 2 - ε / 2 * (Real.pi / 2) := by simp only [w]; ring
    have h : 0 < ε / 2 * (Real.pi / 2) := mul_pos (by linarith) (by linarith)
    linarith
  have hp : 0 < ε ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hε _
  have hL : 0 < L := mul_pos (mul_pos two_pos hw) hp
  have hpr : ε ^ (-(1 / 2) : ℝ) * ε ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hε]
    norm_num
  have hwL : w / L = 1 / 2 * ε ^ (1 / 2 : ℝ) := by
    rw [div_eq_iff hL.ne']
    have : 1 / 2 * ε ^ (1 / 2 : ℝ) * L = w * (ε ^ (-(1 / 2) : ℝ) * ε ^ (1 / 2 : ℝ)) := by
      simp only [L]; ring
    rw [this, hpr, mul_one]
  have hq : 1 < q := by
    refine Real.one_lt_exp_iff.mpr (Real.arsinh_pos_iff.mpr ?_)
    exact div_pos hw hL
  have hprod : 0 < (1 - ε / 2) * (1 - ε / 24) := mul_pos hhalf h24
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hprod.le
  have ht1 : t < 1 := by
    refine (div_lt_one hprod).mpr ?_
    nlinarith [mul_pos hε hε]
  refine ⟨⟨hw, hw2, hL, hwL⟩, hq, ⟨hprod, ht0, ht1⟩, ?_⟩
  intro n hn
  have hqpos : 0 < q := lt_trans one_pos hq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hneg : -(1 - t) / (n : ℝ) < 0 := div_neg_of_neg_of_pos (by linarith) hn0
  exact ⟨Real.rpow_pos_of_pos hqpos _, Real.rpow_lt_one_of_one_lt_of_neg hq hneg⟩
end YangMills.Construction.HolomorphicExtension
end
