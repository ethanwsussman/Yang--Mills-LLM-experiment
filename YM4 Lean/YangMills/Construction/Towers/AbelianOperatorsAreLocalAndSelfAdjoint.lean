import YangMills.Construction.Towers.PropertiesOfAbelianFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def AbelianOperatorsLocalSelfAdjoint : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, AbelianFieldFacts.AbelianOperators θ
end Tower
end YangMills.Construction
end
