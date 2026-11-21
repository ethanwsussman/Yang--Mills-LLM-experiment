import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def IsIntegrableCondExpRepresentative (ρ : Measure (GaugeField a))
    (A Y : GaugeField a → ℂ) : Prop :=
  Measurable[shiftInvariantSigma a] Y ∧ HasFiniteIntegral Y ρ ∧
    ∀ J : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] J → (∃ C : ℝ, ∀ U, ‖J U‖ ≤ C) →
      ∫ U, J U * Y U ∂ρ = ∫ U, J U * A U ∂ρ
def varianceOf (ρ : Measure (GaugeField a)) (X : GaugeField a → ℂ) : ℝ :=
  ∫ U, ‖X U - ∫ V, X V ∂ρ‖ ^ 2 ∂ρ
end InfiniteLattice
end YangMills.Construction
end
