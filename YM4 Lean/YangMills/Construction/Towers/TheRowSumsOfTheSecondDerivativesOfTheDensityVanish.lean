import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def SecondDerivativeRowSumZero : Prop :=
  ∀ z : ℝ, 0 < z → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ e : Tower.FullSpace.PositiveEdge (Tower.meshAt L 0 0),
      HasSum (fun y : Tower.FullSpace.Vertex L 0 0 =>
        secondDerivative z (0 : Tower.FullSpace.Vertex L 0 0) e (Tower.FullSpace.forwardEdge y 1)) 0
end YangMills.Construction.Tower.AbelianFieldDensity
end
