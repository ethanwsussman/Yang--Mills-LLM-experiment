import Mathlib
set_option autoImplicit false
open scoped Classical
noncomputable section
universe u w
namespace YangMills.Construction.PrincipalLog
abbrev principalBranch (z : ℂ) : ℂ := Complex.log z
end YangMills.Construction.PrincipalLog
