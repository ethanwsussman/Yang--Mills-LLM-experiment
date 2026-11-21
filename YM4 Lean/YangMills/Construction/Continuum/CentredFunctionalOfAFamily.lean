import YangMills.Construction.Cumulants.NonSingletonPartitions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SchwingerFunctions
variable {n : ℕ}
def restrictTuple {F : Type*} (X : Fin n → F) (J : Finset (Fin n)) : Fin J.card → F :=
  fun k => X (J.orderEmbOfFin rfl k)
def centredFunctionalOf {E : Type*} (S : (n : ℕ) → (Fin n → (Fin 4 → ℝ) → E) → ℝ)
    (X : Fin n → (Fin 4 → ℝ) → E) : ℝ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts, S J.card (restrictTuple X J)
end SchwingerFunctions
end YangMills.Construction
