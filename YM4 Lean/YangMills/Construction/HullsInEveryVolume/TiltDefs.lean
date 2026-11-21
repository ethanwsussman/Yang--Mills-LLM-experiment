import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction
namespace TorusLimits
def keptSitesAlong (D : ℝ) (r : ℕ) : ℕ := max 1 ⌈D / (82 * (r : ℝ))⌉₊
end TorusLimits
end YangMills.Construction
end
