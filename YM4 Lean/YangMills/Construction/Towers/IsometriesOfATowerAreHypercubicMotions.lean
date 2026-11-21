import YangMills.Construction.Towers.TowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def SymmetriesAreHypercubicMotions : Prop :=
  ∀ L : ℕ, 0 < L → Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    (∀ n : ℕ, 0 < n → TorusSymmetries L n k) ∧ FullSpace.SpaceSymmetries L k
end Tower
end YangMills.Construction
end
