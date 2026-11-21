import YangMills.Construction.Averaging.PinchConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BackgroundRestriction
abbrev holonomyBound (L : ℕ) : ℝ := Averaging.Pinch.holonomyConstant L
end YangMills.Construction.BackgroundRestriction
end
