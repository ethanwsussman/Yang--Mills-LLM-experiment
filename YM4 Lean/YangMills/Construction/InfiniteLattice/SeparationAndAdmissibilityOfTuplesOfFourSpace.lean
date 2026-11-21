import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.SeparationR4
open YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.TestFunctions
variable (M : YangMills.Construction.ReflectionPositivity.AxisMirror.MirrorData)
theorem closedSupport_euclidean_eq_tsupport (f : (Fin 4 → ℝ) → ℝ) :
    (Ambient.closedSupport M .euclidean f : Set (Fin 4 → ℝ)) = tsupport f := by apply _root_.YangMills.Construction.R4TupleForms.closedSupport_euclidean_eq <;> assumption
variable {M}
end YangMills.Construction.InfiniteLattice.SeparationR4
end
