import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def SecondDerivativeShiftInvariant : Prop :=
  ∀ z : ℝ, 0 < z → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (n x y y' : FullSpace.Vertex L 0 0) (μ ν : Fin 4),
      secondDerivative z (x + n) (FullSpace.forwardEdge (y + n) μ) (FullSpace.forwardEdge (y' + n) ν) =
        secondDerivative z x (FullSpace.forwardEdge y μ) (FullSpace.forwardEdge y' ν)
end YangMills.Construction.Tower.AbelianFieldDensity
end
