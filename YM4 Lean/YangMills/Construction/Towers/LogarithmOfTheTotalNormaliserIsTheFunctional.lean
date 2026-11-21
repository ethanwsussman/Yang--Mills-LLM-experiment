import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGaugeOnTheProduct
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LogTotalNormaliserEqFunctional : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k k)
      (HasBackgroundFunctionalFormula L n k)
end YangMills.Construction.Tower
end
