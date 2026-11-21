import YangMills.Construction.Continuum.ConfigurationSpace
import Mathlib
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
def ExistsNearDiagonalPoint : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ x : Config n, ∃ y ∈ fatDiagonal n,
    ENNReal.ofReal (configNorm (x - y)) ≤ ENNReal.ofReal (Real.sqrt 2) * minSeparation x
end YangMills.Construction.ConfigurationSpace
end
