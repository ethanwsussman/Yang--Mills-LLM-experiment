import YangMills.Construction.ReflectionPositivity.WeightsFormAndSeriesOfASplitTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def IntegrateOutProperties : Prop :=
  ∀ (Λ : PeriodSublattice 1) (S : Set Λ.QuotientLink),
    (∀ (f : Λ.QuotientField → ℂ) (C : ℝ), Measurable f → (∀ U, ‖f U‖ ≤ C) →
      Measurable (Λ.integrateOut S f) ∧
      (∀ U, ‖Λ.integrateOut S f U‖ ≤ C) ∧
      PeriodSublattice.DependsOnlyOn (Λ.integrateOut S f) Sᶜ) ∧
    (∀ (f f' : Λ.QuotientField → ℂ) (C : ℝ) (w : ℂ), Measurable f → Measurable f' →
      (∀ U, ‖f U‖ ≤ C) → (∀ U, ‖f' U‖ ≤ C) →
      Λ.integrateOut S (w • f + f') =
        w • Λ.integrateOut S f + Λ.integrateOut S f') ∧
    ∀ (f g : Λ.QuotientField → ℂ) (C : ℝ), Measurable f → Measurable g →
      (∀ U, ‖f U‖ ≤ C) → (∀ U, ‖g U‖ ≤ C) → PeriodSublattice.DependsOnlyOn g Sᶜ →
      ∫ U, g U * f U ∂Λ.quotientHaar = ∫ U, g U * Λ.integrateOut S f U ∂Λ.quotientHaar
end YangMills.Construction.InfiniteLattice
