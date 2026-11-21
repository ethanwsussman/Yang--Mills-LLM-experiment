import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Periodization
open TorusMetric TestFunctions
theorem euclidNormVec_triangle (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
end YangMills.Construction.Periodization
end
