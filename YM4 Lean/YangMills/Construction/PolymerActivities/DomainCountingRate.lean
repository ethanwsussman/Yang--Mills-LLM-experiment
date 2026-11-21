import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PolymerActivities.DomainCounting
def countingRate : ℝ := 22 * Real.log 2
def rateSum (κ : ℝ) : ℝ := 2 ^ 21 * (1 - Real.exp (countingRate - κ))⁻¹
end PolymerActivities.DomainCounting
end YangMills.Construction
end
