import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
noncomputable section
namespace YangMills.Construction.Coordinates.ConstancyOnConnected
open ComplexCoordinates
def IsHolomorphicScalarIn {n : ℕ} (O : Set (ComplexCoordinates n))
    (φ : ComplexCoordinates n → ℂ) : Prop :=
  IsHolomorphicIn O fun z => (Equiv.funUnique (Fin 1) ℂ).symm (φ z)
end YangMills.Construction.Coordinates.ConstancyOnConnected
