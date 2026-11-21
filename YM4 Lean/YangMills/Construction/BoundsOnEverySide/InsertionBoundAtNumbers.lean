import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BoundsOnEverySide
abbrev timeZeroPoint (y : Fin 3 → ℝ) : InfiniteLattice.AmbientSpace := ![y 0, y 1, y 2, 0]
end YangMills.Construction.BoundsOnEverySide
end
