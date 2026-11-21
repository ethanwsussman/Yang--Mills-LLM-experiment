import YangMills.Construction.Towers.PropertiesOfAbelianFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace AbelianFieldPlaquettes
open Tower.AbelianFieldFacts Tower.UnitLatticeL2 Tower.AbelianFieldDensity
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, FaceVariables θ
end AbelianFieldPlaquettes
end Tower
end YangMills.Construction
end
