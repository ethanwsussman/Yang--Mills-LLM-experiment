import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Quaternion ENNReal
noncomputable section
namespace YangMills.Construction.SoftAverages
def expImag (v : Fin 3 → ℝ) : ℍ[ℝ] := NormedSpace.exp (⟨0, v 0, v 1, v 2⟩ : ℍ[ℝ])
end YangMills.Construction.SoftAverages
end
