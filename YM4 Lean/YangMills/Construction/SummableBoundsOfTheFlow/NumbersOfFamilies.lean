import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace FamilyNorms
open TorusLumps
def HasUnitPlaneValue (h : LocalDensity) (v : ℝ) : Prop :=
  HasLimitSecondDeriv h ∧ HasSum (limitFormTerm h unitPlaneCurvature unitPlaneCurvature) v
def curvatureValueLinearityStatement : Prop :=
  ∀ ℓ : StepParameters, ℓ.Admissible →
    (∀ (h h' : LocalDensity) (v v' : ℝ), IsAdmissibleDensity ℓ h → IsAdmissibleDensity ℓ h' →
      HasUnitPlaneValue h v → HasUnitPlaneValue h' v' → HasUnitPlaneValue (h + h') (v + v')) ∧
    (∀ (c : ℝ) (h : LocalDensity) (v : ℝ), IsAdmissibleDensity ℓ h → HasUnitPlaneValue h v →
      HasUnitPlaneValue (c • h) (c * v)) ∧
    (∀ (h h' : LocalDensity) (v v' : ℝ), IsAdmissibleDensity ℓ h → IsAdmissibleDensity ℓ h' →
      HasCurvatureForm h v → HasCurvatureForm h' v' → HasCurvatureForm (h + h') (v + v')) ∧
    ∀ (c : ℝ) (h : LocalDensity) (v : ℝ), IsAdmissibleDensity ℓ h → HasCurvatureForm h v →
      HasCurvatureForm (c • h) (c * v)
end FamilyNorms
end YangMills.Construction
end
