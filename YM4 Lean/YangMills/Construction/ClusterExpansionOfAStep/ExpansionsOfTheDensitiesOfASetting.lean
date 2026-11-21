import YangMills.Construction.ClusterExpansionOfAStep.PartsOfAPotential
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open RenormalizationStepParameters
def totalDensityPieceBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C c y₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup,
    R.OnParameters T y → ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
      s.IsPotentialPiece s.totalDensity (C * (1 + T.E₃) + R.coupling ^ C * Real.exp (-c * (R.range : ℝ)))
end YangMills.Construction.StepSettings
end
