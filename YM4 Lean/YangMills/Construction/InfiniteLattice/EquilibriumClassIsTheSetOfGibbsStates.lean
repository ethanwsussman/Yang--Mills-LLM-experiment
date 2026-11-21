import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def GibbsClassEqGibbsStates : Prop :=
  (∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β → ∀ ν : Measure (GaugeField a),
    IsProbabilityMeasure ν →
      List.TFAE
        [ν ∈ gibbsClass ha β,
          ∀ W : LinkWindow a, ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
            ∫ U, W.conditionalExpectation ha β F U ∂ν = ∫ U, F U ∂ν,
          IsGibbs β ν]) ∧
  (∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β →
    gibbsClass ha β = {ν | IsGibbs β ν} ∧
      periodicGibbsClass ha β = {ν | IsPeriodicGibbs β ν}) ∧
  (∀ L : ℕ, Odd L → 13 ≤ L → ∀ (J : ℕ) (ha : 0 < PeriodicLattice.meshSize L (J : ℤ)) (β : ℝ), 0 < β →
    periodicGibbsClass ha β = periodicGibbsSet L J β)
end YangMills.Construction.InfiniteLattice
