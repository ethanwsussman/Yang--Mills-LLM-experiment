import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Pointwise
noncomputable section
namespace YangMills.Construction.TorusMetric
variable {S : ℝ}
theorem supNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ supNormVec v :=
  (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
end YangMills.Construction.TorusMetric
end
