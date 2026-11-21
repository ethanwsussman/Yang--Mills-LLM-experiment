import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours TorusFields TorusLumps RenormalizationStepParameters
def StepSetup.MarkedIntegralInvariant (R : StepSetup) : Prop :=
  ∀ n [NeZero n], R.params.n₀ ≤ n → ∀ (V : TorusField n) (A : Finset (TorusSite n)),
    IsCold (9 / 8 * R.params.threshold) V →
    (∀ g : TorusSite n → UnitQuaternion, R.markedIntegral A (gaugeTransform g V) = R.markedIntegral A V) ∧
    ∀ u : TorusSite n, R.markedIntegral A (TorusFields.translate u V) = R.markedIntegral (A.image (· + u)) V
end YangMills.Construction.StepSettings
namespace YangMills.Construction.StepInvariance
open BlockAverages LumpContours TorusFields TorusLumps RenormalizationStepParameters StepSettings
def MarkedIntegralInvariance : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
      R.MarkedIntegralInvariant
end YangMills.Construction.StepInvariance
end
