import YangMills.Construction.HilbertSpace.FormCompletionsAndBorelPVMs
import YangMills.Construction.InfiniteLattice.RulesForObservablesIsometriesAndMirrors
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def LocalDeterminationAndIntegrableAction : Prop :=
  ∀ (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν] (g : UnitLatticeSymmetry),
    ((∀ (ν' : Measure (GaugeField 1)) [IsProbabilityMeasure ν'],
        (∀ F : GaugeField 1 → ℂ, IsBoundedObservable F → IsLocalObservable F →
          ∫ U, F U ∂ν' = ∫ U, F U ∂ν) → ν' = ν) ∧
      ((∀ F : GaugeField 1 → ℂ, IsBoundedObservable F → IsLocalObservable F →
          ∫ U, g.actOn F U ∂ν = ∫ U, F U ∂ν) → IsSymmetricUnder ν g)) ∧
    (∀ p : ℝ≥0∞, (p = 1 ∨ p = 2) → ∀ (f : Lp ℂ p ν) (ε : ℝ), 0 < ε →
      ∃ H : GaugeField 1 → ℂ, Continuous H ∧ IsBoundedObservable H ∧ IsLocalObservable H ∧
        eLpNorm (⇑f - H) p ν ≤ ENNReal.ofReal ε) ∧
    ((IsSymmetricUnder ν (LatticeSymmetry.refl 1) ∧
        (∀ g₁ g₂ : UnitLatticeSymmetry, IsSymmetricUnder ν g₁ → IsSymmetricUnder ν g₂ →
          IsSymmetricUnder ν (g₁ * g₂)) ∧
        (∀ g₁ : UnitLatticeSymmetry, IsSymmetricUnder ν g₁ →
          (∃ k : UnitLatticeSymmetry, k.IsInverse g₁) ∧
          ∀ k : UnitLatticeSymmetry, k.IsInverse g₁ → IsSymmetricUnder ν k)) ∧
      (IsSymmetricUnder ν g →
        (∀ f : GaugeField 1 → ℂ, Measurable f → (∀ U, 0 ≤ f U) →
          ∫⁻ U, ‖g.actOn f U‖ₑ ∂ν = ∫⁻ U, ‖f U‖ₑ ∂ν) ∧
        (∀ f : GaugeField 1 → ℂ, Measurable f → Integrable f ν →
          Integrable (g.actOn f) ν ∧
          ∫ U, g.actOn f U ∂ν = ∫ U, f U ∂ν ∧
          eLpNorm (g.actOn f) 1 ν = eLpNorm f 1 ν) ∧
        (∀ f f' : GaugeField 1 → ℂ, Measurable f → Measurable f' → f =ᵐ[ν] f' →
          g.actOn f =ᵐ[ν] g.actOn f') ∧
        ∃ V : Lp ℂ 2 ν ≃ₗ[ℂ] Lp ℂ 2 ν,
          FormHilbert.IsUnitaryLinearMap (V : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν) ∧
          (∀ f : Lp ℂ 2 ν, ⇑(V f) =ᵐ[ν] g.actOn ⇑f) ∧
          ∀ k : UnitLatticeSymmetry, k.IsInverse g →
            ∀ f : Lp ℂ 2 ν, ⇑(V.symm f) =ᵐ[ν] k.actOn ⇑f))
end YangMills.Construction.InfiniteLattice
