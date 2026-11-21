import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
def KernelGaugeInvariance : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (n : ℕ) [NeZero n] (g : TorusSite n → UnitQuaternion)
    (W : TorusField (n * ℓ.side)) (V : TorusField n),
    fineHotLumps ℓ (fineLevelField ℓ n (gaugeTransform (blockConstantGauge ℓ.side g) W)) =
        fineHotLumps ℓ (fineLevelField ℓ n W) ∧
    baseChoices ℓ (fineLevelField ℓ n (gaugeTransform (blockConstantGauge ℓ.side g) W)) =
        baseChoices ℓ (fineLevelField ℓ n W) ∧
    ∀ x : ℝ,
      (∀ b ∈ baseChoices ℓ (fineLevelField ℓ n W), ∀ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        bondKernel ℓ x (fineLevelField ℓ n (gaugeTransform (blockConstantGauge ℓ.side g) W))
            (coarseLevelField ℓ n (gaugeTransform g V)) b c =
          bondKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V) b c) ∧
      averagedKernel ℓ x (fineLevelField ℓ n (gaugeTransform (blockConstantGauge ℓ.side g) W))
          (coarseLevelField ℓ n (gaugeTransform g V)) =
        averagedKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V)
end TorusLumps
end YangMills.Construction
end
