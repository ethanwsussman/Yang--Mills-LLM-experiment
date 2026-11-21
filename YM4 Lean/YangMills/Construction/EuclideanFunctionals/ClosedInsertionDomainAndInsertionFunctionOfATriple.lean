import YangMills.Construction.EuclideanFunctionals.ComplexExtensionDomain
import YangMills.Construction.EuclideanFunctionals.RulesOfMotionsConcatenationAndComplexEntries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def closedComplexExtensionDomain (η : ℝ) : Set (Fin 4 → ℂ) :=
  {z | complexExtensionGauge z ≤ η / 8}
def tripleInsertionFn (S : ConnFamily) (F : FreeSep) (k : R4 → ℝ) (A : FreeSep)
    (x : R4) : ℂ :=
  insertion S F
    (MotionMulRules.shiftFn x fun y => (k y : ℂ)) A
end YangMills.Construction.EuclideanFunctionals
