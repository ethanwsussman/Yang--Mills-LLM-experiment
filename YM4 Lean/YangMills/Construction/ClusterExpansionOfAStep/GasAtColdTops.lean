import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours TorusFields TorusLumps RenormalizationStepParameters
def StepSetup.MarkedIntegralStable (R : StepSetup) (ch : ℝ) : Prop :=
  ∀ n [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * R.params.threshold) V →
    ∀ (A : Finset (TorusSite n)) (Y : TorusSite n), 0 < R.markedIntegral A V ∧
      (1 - Real.exp (-(7 * ch * R.coupling))) * R.markedIntegral A V ≤ R.markedIntegral (insert Y A) V ∧
      R.markedIntegral (insert Y A) V ≤ R.markedIntegral A V
def StepSetup.DensitiesLocal (R : StepSetup) (ch : ℝ) : Prop :=
  ∀ n n' [NeZero n] [NeZero n'], R.params.n₀ ≤ n → R.params.n₀ ≤ n' → ∀ (V : TorusField n) (V' : TorusField n')
    (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ), 1 ≤ m → 2 * m + 2 < n → 2 * m + 2 < n' →
    IsCold (9 / 8 * R.params.threshold) V → IsCold (9 / 8 * R.params.threshold) V' → FieldsAgreeNear V V' Y Y' m →
    |R.blockDensity n Y V - R.blockDensity n' Y' V'| ≤ Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)
end YangMills.Construction.StepSettings
namespace YangMills.Construction.StepGas
open BlockAverages LumpContours TorusFields TorusLumps RenormalizationStepParameters StepSettings
def ColdGasBounds : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
      R.MarkedIntegralStable T.gasRate ∧ R.DensitiesLocal T.gasRate
end YangMills.Construction.StepGas
end
