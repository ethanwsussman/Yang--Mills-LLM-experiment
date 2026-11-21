import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps
namespace FamilyNorms
def equalTotalsEqualLimitStatement : Prop :=
  ∀ ℓ : StepParameters, ℓ.Admissible → ∀ (C : ℝ) (h h' : LocalDensity) (v v' : ℝ),
    IsCurvatureFamily ℓ C h → IsCurvatureFamily ℓ C h' →
    (∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
      ∑ y, centered h n y V = ∑ y, centered h' n y V) →
    HasSum (limitFormTerm h unitPlaneCurvature unitPlaneCurvature) v →
    HasSum (limitFormTerm h' unitPlaneCurvature unitPlaneCurvature) v' → v = v'
end FamilyNorms
end YangMills.Construction
end
