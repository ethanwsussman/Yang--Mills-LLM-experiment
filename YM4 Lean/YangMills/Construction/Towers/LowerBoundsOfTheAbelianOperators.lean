import YangMills.Construction.Towers.PropertiesOfAbelianFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianOperatorBounds
open Tower.AbelianFieldFacts Tower.UnitLatticeL2
def LowerBoundsHold : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, SpectralLowerBounds θ
end YangMills.Construction.Tower.AbelianOperatorBounds
end
