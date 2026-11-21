import YangMills.Construction.Torus.LiftsShapeConditionAndCollinearQuadruples
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.TestFunctions YangMills.Construction.PeriodicLattice YangMills.Construction.QuadrupleClasses
namespace YangMills.Construction.FourPointBounds
def UnitScalePairOfQuadruple : Prop :=
  ∀ (s : Conventions.StandingParameters) (d v : ℝ) (f : Fin 4 → s.Torus → ℝ), f ∈ collinearQuadsTorus s d v →
    ∃ φ ψ : (Fin 4 → ℝ) → ℝ, (φ, ψ) ∈ separatedPairsR4 1 v ∧ uniformNorm φ = 1 ∧ uniformNorm ψ = 1
end YangMills.Construction.FourPointBounds
end
