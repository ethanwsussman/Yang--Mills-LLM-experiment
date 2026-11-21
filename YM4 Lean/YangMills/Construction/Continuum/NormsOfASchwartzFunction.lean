import YangMills.Construction.Continuum.SchwartzFunctionsFlatOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace
abbrev SchwartzFn (n : ℕ) : Type := {f : Config n → ℂ // IsSchwartz f}
variable {n : ℕ}
def bracketNorm (k : ℕ) (f : SchwartzFn n) : ℝ := (schwartzSeminorm k f.1).toReal
end ConfigSpace
end YangMills.Construction
end
