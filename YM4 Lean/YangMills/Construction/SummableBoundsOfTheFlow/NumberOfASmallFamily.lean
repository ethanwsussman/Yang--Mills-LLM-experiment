import YangMills.Construction.SummableBoundsOfTheFlow.NumbersOfFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilyNorms
open TorusLumps
def smallFamilyValueStatement : Prop :=
  ∀ (P : TorusLumps.StepParameters) (C : ℝ) (g : LocalDensity), P.Admissible → 0 ≤ C → IsCurvatureFamily P C g →
    ∃ v, HasUnitPlaneValue g v ∧ |v| ≤ C * potentialWeightSum P.rt P.n₁
end YangMills.Construction.FamilyNorms
end
