import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames.Adjoint
open BlockOffsets
theorem coe_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ((adjointAction g X : imaginaryQuaternions) : ℍ[ℝ]) =
      (g : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    adjointAction g (X + Y) = adjointAction g X + adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
theorem adjointAction_zero (g : UnitQuaternion) : adjointAction g 0 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (r : ℝ) (X : imaginaryQuaternions) :
    adjointAction g (r • X) = r • adjointAction g X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_smul <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ‖adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
theorem coe_mul_coe_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem expUnit_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    expUnit (adjointAction g w) = g * expUnit w * g⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.expUnit_adjointAction <;> assumption
end ColdStepAtMirrorFrames.Adjoint
end YangMills.Construction
end
