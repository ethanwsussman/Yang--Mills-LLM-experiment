import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
def HaarIntegralInLogCoords : Prop :=
  ∀ ψ : UnitQuaternion → ℝ, Continuous ψ →
    ∫ g, ψ g ∂haarUnit = ∫ v : EuclideanSpace ℝ (Fin 3), haarLogDensity v * ψ (expUnit (toImaginary v))
end YangMills.Construction.ColdStepAtMirrorFrames
end
