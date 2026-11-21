import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours TorusFields TorusLumps RenormalizationStepParameters StepSettings
def StepSettings.StepSetup.LogMarkedIntegralSmooth (R : StepSetup) (C : ℝ) : Prop :=
  ∀ n [NeZero n], R.params.n₀ ≤ n → ∀ (A : Finset (TorusSite n)) (V : TorusField n) (k : ℕ)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ),
    IsCold (9 / 8 * R.params.threshold) (perturb c X τ V) →
    ContDiffAt ℝ 40 (fun τ' => Real.log (R.markedIntegral A (perturb c X τ' V))) τ ∧
    (k ≤ 3 → AreUnitVectors X →
      ‖iteratedFDeriv ℝ 40 (fun τ' => Real.log (R.markedIntegral A (perturb c X τ' V))) τ‖ ≤ R.coupling ^ C)
def ClusterExpansionOfAStep.LogMarkedIntegralDerivativesBounded : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ C y₀ : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
      R.LogMarkedIntegralSmooth C
end YangMills.Construction
end
