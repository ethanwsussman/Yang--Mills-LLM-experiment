import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
def IsNonnegComplex (z : ℂ) : Prop :=
  z ∈ Complex.ofReal '' Set.Ici (0 : ℝ)
end YangMills.Construction.PeriodicSpace
