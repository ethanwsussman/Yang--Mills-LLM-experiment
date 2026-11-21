import YangMills.Construction.TotalDensitiesGiveASystem.TheCyclicFormulaAtSeparatedTuples
import YangMills.Construction.TotalDensitiesGiveASystem.TheShortDistanceLawIsNotGaussian
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
theorem shortDistanceNonGaussian_of_cyclicFormula (h : CyclicFormulaOnSeparatedTuples) :
    TotalDensities.ShortDistanceNonGaussianAtEveryShape.Statement := fun ϑ hϑ =>
  ⟨fun n _ hn hodd _ X => h.1 n hn hodd X, fun X hX => h.2 ϑ hϑ X hX⟩
end YangMills.Construction.TotalDensitiesGiveASystem
end
