import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open RenormalizationStepParameters StepSettings TorusFields TorusLumps
def HotFactorization : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
      IsSmallDensity R.params (Real.exp (-(T.gasRate * R.coupling / 2))) R.blockDensity ∧
        ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold T.threshold V →
          0 < coldImageIntegral R V ∧ 0 < kernelImage R.params R.coupling R.functional n V ∧
          Real.log (kernelImage R.params R.coupling R.functional n V) =
            Real.log (coldImageIntegral R V) + ∑ Y, R.blockDensity n Y V
end YangMills.Construction.ClusterExpansionOfAStep
end
