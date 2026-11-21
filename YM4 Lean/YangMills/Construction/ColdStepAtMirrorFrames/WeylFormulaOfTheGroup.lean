import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
def WeylIntegrationFormula : Prop :=
  (∀ φ : ℝ → ℝ, Continuous φ →
    ∫ g : UnitQuaternion, φ (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re) ∂haarUnit =
      ∫ v in (0 : ℝ)..2, φ v * haarRealPartDensity v) ∧
  (∀ s : ℝ, partitionFn s = haarCharacterMean s) ∧ ∀ s : ℝ, logPartitionGap s = haarGap s
end YangMills.Construction.ColdStepAtMirrorFrames
end
