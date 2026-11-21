import YangMills.Construction.InfiniteLattice.PureAndErgodicMeasuresOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.ShiftInvariantConditioningAndPlateau
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def ExtremalErgodicPeriodicGibbsStatement : Prop :=
  ∀ β : ℝ, 0 < β →
    (∀ μ₁ ∈ periodicGibbsUnit β, ∀ μ₂ ∈ periodicGibbsUnit β,
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ENNReal.ofReal t • μ₁ + ENNReal.ofReal (1 - t) • μ₂ ∈ periodicGibbsUnit β) ∧
    (∀ μ : Measure (GaugeField (1 : ℝ)), IsUnitShiftErgodic μ →
      (∀ J : GaugeField (1 : ℝ) → ℂ, Measurable[shiftInvariantSigma 1] J →
        (∃ C : ℝ, ∀ U, ‖J U‖ ≤ C) → ∀ᵐ U ∂μ, J U = ∫ V, J V ∂μ) ∧
      (∀ B : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable B →
        ∀ᵐ U ∂μ, condExpGiven μ (shiftInvariantSigma 1) B U = ∫ V, B V ∂μ)) ∧
    (∀ μ : Measure (GaugeField (1 : ℝ)), IsExtremalUnitPeriodicGibbs β μ →
      IsUnitShiftErgodic μ) ∧
    ((∀ μ ∈ periodicGibbsUnit β, IsShiftInvariant μ) →
      ∀ μ ∈ periodicGibbsUnit β, IsUnitShiftErgodic μ →
        IsExtremalUnitPeriodicGibbs β μ)
end YangMills.Construction.InfiniteLattice
