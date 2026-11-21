import YangMills.Construction.Towers.PropertiesOfAbelianFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def MassiveOperatorQuadraticForm : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, AbelianFieldFacts.HessianQuadraticForm θ
end YangMills.Construction.Tower
end
