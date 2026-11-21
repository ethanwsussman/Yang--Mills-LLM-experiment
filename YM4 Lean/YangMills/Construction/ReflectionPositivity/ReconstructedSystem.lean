import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.QuantumSystem
def forwardCone : Set (Fin 2 → ℝ) := {y | |y 1| ≤ y 0}
end ReflectionPositivity.QuantumSystem
end YangMills.Construction
end
