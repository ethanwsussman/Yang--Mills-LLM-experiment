import YangMills.Construction.HoleBesideASecondHole.FitOfANearMean
import YangMills.Construction.HoleBesideASecondHole.MeanOfAProductOfGroupVariablesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open BlockAverages GroupMeans
namespace NearMeanFit
theorem unitQuaternion_norm (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem coe_mul_coe_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem coe_mul_eq (g g' : UnitQuaternion) :
    ((g * g' : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (g' : ℍ[ℝ]) := rfl
theorem norm_mul_unit (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖q * (g : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, unitQuaternion_norm, mul_one]
theorem norm_sub_one_sq (z : UnitQuaternion) : ‖(z : ℍ[ℝ]) - 1‖ ^ 2 = 2 - 2 * (z : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.GaugeFixing.norm_coe_sub_one_sq <;> assumption
theorem norm_smul_polarPart (q : ℍ[ℝ]) : (‖q‖ : ℝ) • ((polarPart q : UnitQuaternion) : ℍ[ℝ]) = q := by apply _root_.YangMills.Construction.GroupMeans.norm_smul_polarPart <;> assumption
theorem norm_sub_re_mul_inv_eq (q : ℍ[ℝ]) (V : UnitQuaternion) :
    ‖q‖ - (q * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      ‖q‖ * (‖((polarPart q : UnitQuaternion) : ℍ[ℝ]) - V‖ ^ 2 / 2) := by
  have h1 : ‖((polarPart q : UnitQuaternion) : ℍ[ℝ]) - V‖ =
      ‖((polarPart q * V⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
    rw [← norm_mul_unit V⁻¹]
    congr 1
    rw [sub_mul, coe_mul_coe_inv, coe_mul_eq]
  have h2 := norm_sub_one_sq (polarPart q * V⁻¹)
  have hq : q = (‖q‖ : ℝ) • ((polarPart q : UnitQuaternion) : ℍ[ℝ]) := (norm_smul_polarPart q).symm
  have h3 : (q * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      ‖q‖ * ((polarPart q * V⁻¹ : UnitQuaternion) : ℍ[ℝ]).re := by
    conv_lhs => rw [hq]
    rw [smul_mul_assoc, Quaternion.re_smul, coe_mul_eq]
    rfl
  rw [h1, h2, h3]
  ring
end NearMeanFit
theorem nearMeanFitEstimate_holds : NearMeanFitEstimate := by
  intro Q Q' V D hD hD2 hQ hQ' h1 h1' hd
  have e := NearMeanFit.norm_sub_re_mul_inv_eq Q V
  have e' := NearMeanFit.norm_sub_re_mul_inv_eq Q' V
  set A := ‖((polarPart Q : UnitQuaternion) : ℍ[ℝ]) - V‖ with hA
  set A' := ‖((polarPart Q' : UnitQuaternion) : ℍ[ℝ]) - V‖ with hA'
  set r := ‖Q‖ with hr
  set r' := ‖Q'‖ with hr'
  set f := r - (Q * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ])).re with hf
  rw [e']
  have hA'0 : 0 ≤ A' := norm_nonneg _
  have hAA : A' ≤ A + D := by
    have e1 : ((polarPart Q' : UnitQuaternion) : ℍ[ℝ]) - V =
        (((polarPart Q : UnitQuaternion) : ℍ[ℝ]) - V) -
          (((polarPart Q : UnitQuaternion) : ℍ[ℝ]) - (polarPart Q' : UnitQuaternion)) := by abel
    rw [hA', e1]
    have := norm_sub_le (((polarPart Q : UnitQuaternion) : ℍ[ℝ]) - V)
      (((polarPart Q : UnitQuaternion) : ℍ[ℝ]) - (polarPart Q' : UnitQuaternion))
    linarith
  have hrh : 1 / 2 ≤ r := by linarith
  have hf2 : f = r * (A ^ 2 / 2) := e
  have hsq : A ≤ 2 * Real.sqrt f := by
    have h4 : A ^ 2 ≤ 4 * f := by
      rw [hf2]
      nlinarith [sq_nonneg A]
    have h5 : A ≤ Real.sqrt (4 * f) := Real.le_sqrt_of_sq_le h4
    have h6 : Real.sqrt (4 * f) = 2 * Real.sqrt f := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    linarith
  have hhalf : A ^ 2 / 2 ≤ f * (1 + 2 * D) := by
    rw [hf2]
    have h7 : 1 ≤ r * (1 + 2 * D) := by nlinarith
    nlinarith
  have hmain : r' * (A' ^ 2 / 2) ≤ (A + D) ^ 2 / 2 := by
    have h9 : A' ^ 2 ≤ (A + D) ^ 2 := pow_le_pow_left₀ hA'0 hAA 2
    nlinarith
  have hAD : A * D ≤ 2 * D * Real.sqrt f := by nlinarith
  nlinarith [sq_nonneg D]
end YangMills.Construction.LumpContours
end
