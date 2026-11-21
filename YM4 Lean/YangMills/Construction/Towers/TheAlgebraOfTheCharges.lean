import YangMills.Construction.Towers.PropertiesOfAbelianFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ChargeAlgebraAndForms : Prop :=
  AbelianFieldFacts.ChargeAlgebra ∧
    ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
      AbelianFieldFacts.FormsChargeDecomposition (meshAt L 0 0)
end YangMills.Construction.Tower
end
