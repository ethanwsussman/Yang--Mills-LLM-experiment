import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.TestFunctions
open YangMills.Construction.TorusMetric
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
end YangMills.Construction.TestFunctions
