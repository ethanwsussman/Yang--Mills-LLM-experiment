import YangMills.Construction.Towers.PropertiesOfAbelianFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianActionGradient
open YangMills.Construction.Tower.AbelianFieldFacts YangMills.Construction.Tower.UnitLatticeL2
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, ActionDerivative θ
end YangMills.Construction.Tower.AbelianActionGradient
end
