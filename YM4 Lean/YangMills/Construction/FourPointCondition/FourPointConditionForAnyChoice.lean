import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def fourPointBoundAtEveryProfile : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ vt : ℝ, 0 < vt → vt ≤ 1 →
    ∀ (R : CouplingEvaluation) (lam Ca d₀ : ℝ) (n₀ : ℕ), EvaluationLaws R (Tb.stepParameters y).side vt lam Ca d₀ n₀ →
      ∃ d₄ ∈ Ioc (0 : ℝ) d₀, FourPointConditionHolds R (Tb.stepParameters y).side vt d₄ n₀
end YangMills.Construction.FourPointCondition
end
