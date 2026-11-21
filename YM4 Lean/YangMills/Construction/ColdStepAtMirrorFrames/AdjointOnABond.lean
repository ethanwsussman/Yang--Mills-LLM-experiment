import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def AdjointActionLinearIsometry : Prop :=
  ∀ g : UnitQuaternion, ∃ A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
    ∀ v, toImaginary (A v) = adjointAction g (toImaginary v)
end YangMills.Construction.ColdStepAtMirrorFrames
end
