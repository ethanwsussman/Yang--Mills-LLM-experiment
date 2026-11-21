import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
namespace YangMills.Construction.Coordinates.ComplexCoordinates
namespace HolomorphicDifferentiable
def HolomorphicIffDifferentiableStatement : Prop :=
  ∀ (N N' : ℕ) (U : Set (ComplexCoordinates N)) (f : ComplexCoordinates N → ComplexCoordinates N'),
    IsOpen U → (IsHolomorphicIn U f ↔ DifferentiableOn ℂ f U)
end HolomorphicDifferentiable
end YangMills.Construction.Coordinates.ComplexCoordinates
