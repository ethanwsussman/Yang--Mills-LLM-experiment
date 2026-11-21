import YangMills.Construction.InfiniteLattice.DilationCarriesStatesToSpacingOneProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
theorem continuous_gaugeFieldUnrescale (ha : 0 < a) :
    Continuous (gaugeFieldUnrescale ha) := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.ScalingToUnitSpacing.continuous_gaugeFieldUnrescale <;> assumption
end YangMills.Construction.InfiniteLattice
