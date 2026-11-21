import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveStiffnessFunctions
open PeriodicOperators.Tempered (IsLatticeFunctional)
def FieldFamilyIsFunctional : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    IsLatticeFunctional L (massiveFieldFamily L z)
end YangMills.Construction.Tower.MassiveStiffnessFunctions
end
