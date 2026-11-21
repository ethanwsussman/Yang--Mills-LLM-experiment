import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def LevelSharesUniformAt (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ,
    TorusLumps.IsCurvatureFamily (Tb.stepParameters y) C
      (ShareFamilies.levelShareFamily (Tb.stepParameters y).coupling (Tb.stepParameters y).side t) ∧
    ∀ (n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n → ∀ z : TorusFields.TorusSite n,
      StepCosts.levelShare (Tb.stepParameters y).coupling (Tb.stepParameters y).side t Finset.univ z
        (TorusFields.trivialField n) = 0
def levelSharesUniformStatement : Prop := HoldsOnParameterFamilies LevelSharesUniformAt
end YangMills.Construction.ResponseInTheExpansion
end
