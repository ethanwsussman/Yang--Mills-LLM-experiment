import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.Measurability.FactorThroughMap
def Claim : Prop :=
  ∀ (S Y : Type) (mY : MeasurableSpace Y) (f : S → Y) (g : S → ℂ),
    Measurable[mY.comap f] g →
      (∃ h : Y → ℂ, Measurable h ∧ g = h ∘ f) ∧
      ∀ c : ℝ, 0 ≤ c → (∀ s, ‖g s‖ ≤ c) →
        ∃ h : Y → ℂ, Measurable h ∧ g = h ∘ f ∧ ∀ y, ‖h y‖ ≤ c
end YangMills.Construction.Measurability.FactorThroughMap
