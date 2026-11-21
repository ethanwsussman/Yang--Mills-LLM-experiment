import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGaugeOnTheProduct
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k : ℕ}
structure LogNormaliserRepresentation (L n k : ℕ) : Prop where
  wellDefined_at_identity : Tower.BackgroundFunctionalWellDefined (Tower.trivialField L n k 0) 0 0
  analytic_near_identity : Tower.BackgroundFunctionalAnalyticNearIdentity L n k
  gauge_invariant : Tower.ForGaugesNearOneOrConstant (L := L) (n := n) (k := k) (j := 0)
    Tower.BackgroundFunctionalGaugeInvariant
  eventually_formula : Tower.EventuallyNearIdentity (Tower.fieldSpace L n k k)
    (Tower.HasBackgroundFunctionalFormula L n k)
def LogNormaliserRepresentationHolds : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    Tower.LogNormaliserRepresentation L n k
end YangMills.Construction.Tower
end
