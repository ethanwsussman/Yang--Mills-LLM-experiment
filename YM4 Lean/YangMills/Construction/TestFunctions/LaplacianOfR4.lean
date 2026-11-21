import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TestFunctions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def laplacianR4 (f : (Fin 4 → ℝ) → E) : (Fin 4 → ℝ) → E :=
  fun x => ∑ μ, partialDerivR4 μ (partialDerivR4 μ f) x
end TestFunctions
end YangMills.Construction
end
