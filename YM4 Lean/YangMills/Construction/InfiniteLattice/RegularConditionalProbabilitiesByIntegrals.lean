import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def IsRegularConditionalByIntegrals (ν : Measure (GaugeField a))
    (κ : GaugeField a → GaugeFieldProbability a) : Prop :=
  ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    Measurable[shiftInvariantSigma a] (fun U => (κ U).expect F) ∧
      ∀ J : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] J → (∃ C : ℝ, ∀ U, ‖J U‖ ≤ C) →
        ∫ U, J U * (κ U).expect F ∂ν = ∫ U, J U * F U ∂ν
end YangMills.Construction.InfiniteLattice
