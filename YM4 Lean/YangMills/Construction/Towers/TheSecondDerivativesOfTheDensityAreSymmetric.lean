import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def SecondDerivativeSymm : Prop :=
  ∀ z : ℝ, 0 < z → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (x : Tower.FullSpace.Vertex L 0 0) (e e' : Tower.FullSpace.PositiveEdge (Tower.meshAt L 0 0)),
      secondDerivative z x e e' = secondDerivative z x e' e
end YangMills.Construction.Tower.AbelianFieldDensity
end
