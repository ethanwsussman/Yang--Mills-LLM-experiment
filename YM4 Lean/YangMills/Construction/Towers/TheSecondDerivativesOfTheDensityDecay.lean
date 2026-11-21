import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def SecondDerivativeExpDecay : Prop :=
  ∀ z : ℝ, 0 < z → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ C c : ℝ, 0 < c ∧
    ∀ (x : FullSpace.Vertex L 0 0) (b b' : FullSpace.PositiveEdge (meshAt L 0 0)),
      ‖secondDerivative z x b b'‖ ≤ C * Real.exp (-c *
        (TorusMetric.euclidNormVec ((x - b.1.initial : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace) +
          TorusMetric.euclidNormVec ((x - b'.1.initial : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace)))
end YangMills.Construction.Tower.AbelianFieldDensity
end
