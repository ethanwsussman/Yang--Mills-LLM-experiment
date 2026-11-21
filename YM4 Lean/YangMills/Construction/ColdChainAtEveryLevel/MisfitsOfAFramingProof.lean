import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.MisfitsOfAFraming
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
namespace GaugedMisfit
theorem coe_mul_unit (a b : UnitQuaternion) :
    ((a * b : UnitQuaternion) : ℍ[ℝ]) = (a : ℍ[ℝ]) * (b : ℍ[ℝ]) := rfl
theorem polarUnit_conj (g g' : UnitQuaternion) {q : ℍ[ℝ]} (h : q ≠ 0) :
    polarUnit ((g : ℍ[ℝ]) * q * ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])) = g * polarUnit q * g'⁻¹ := by apply _root_.YangMills.Construction.GaugeMotions.polarUnit_coe_mul_mul_coe_inv <;> assumption
theorem coe_conj_gaugeTransform (G k γ G' k' γ' : UnitQuaternion) (M : ℍ[ℝ]) :
    ((G * k * γ⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((γ : ℍ[ℝ]) * M * ((γ'⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
        (((G' * k' * γ'⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (G : ℍ[ℝ]) * ((k : ℍ[ℝ]) * M * ((k'⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
        ((G'⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  have e1 : (((G * k * γ⁻¹) * γ : UnitQuaternion) : ℍ[ℝ]) = ((G * k : UnitQuaternion) : ℍ[ℝ]) := by
    congr 1
    group
  have e2 : ((γ'⁻¹ * (G' * k' * γ'⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      ((k'⁻¹ * G'⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    congr 1
    group
  rw [coe_mul_unit] at e1 e2
  calc ((G * k * γ⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((γ : ℍ[ℝ]) * M * ((γ'⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
        (((G' * k' * γ'⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])
      = (((G * k * γ⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (γ : ℍ[ℝ])) * M *
          (((γ'⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (((G' * k' * γ'⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
        simp only [mul_assoc]
    _ = _ := by
        rw [e1, e2]
        simp only [Submonoid.coe_mul, mul_assoc]
end GaugedMisfit
open GaugedMisfit in
theorem gaugedMisfitNorm_holds (hG : gaugeCovarianceStatement) : gaugedMisfitNormStatement := by
  intro F W kW X k Γ j c hL hj htop hbal hq
  obtain ⟨-, hcov, -, -⟩ := hG F j hj hL
  have hmean : gaugedContourAverage (gaugedChainFields X Γ j)
        (balancedLinkAgainst W kW (gaugedChainFields X Γ) j) c =
      (rotationAboveLevel W kW X k Γ j c.1 : ℍ[ℝ]) * gaugedContourAverage (X j) (k (j + 1)) c *
        (((rotationAboveLevel W kW X k Γ j (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    unfold gaugedContourAverage
    rw [show gaugedChainFields X Γ j = gaugeTransform (Γ j) (X j) from rfl]
    rw [← show gaugedChainFields X Γ j = gaugeTransform (Γ j) (X j) from rfl]
    rw [show contourAverage (gaugedChainFields X Γ j) c = _ from hcov (Γ j) (X j) c]
    rw [balancedLinkAgainst_eq_rotationAboveLevel W kW X k Γ j c.1,
      balancedLinkAgainst_eq_rotationAboveLevel W kW X k Γ j (c.1 + unitStep (j + 1) c.2)]
    exact coe_conj_gaugeTransform _ _ _ _ _ _ _
  have hup := framedUpperField_eq_gaugeTransform W kW X k Γ hj htop hbal
  have e : bondMisfit (gaugedChainFields X Γ j) (balancedLinkAgainst W kW (gaugedChainFields X Γ) j)
        (framedUpperField W kW X k Γ j) c =
      rotationAboveLevel W kW X k Γ j c.1 * bondMisfit (X j) (k (j + 1)) (X (j + 1)) c *
        (rotationAboveLevel W kW X k Γ j c.1)⁻¹ := by
    unfold bondMisfit
    rw [hmean, polarUnit_conj _ _ hq, hup]
    simp only [gaugeTransform]
    group
  unfold distFromOne
  rw [e, norm_coe_conj_sub_one]
end YangMills.Construction.BlockAverages
end
