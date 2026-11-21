import YangMills.Construction.InfiniteLattice.CountableDenseFamilyOfLocalFunctions
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.RegularConditionalProbabilitiesByIntegrals
import YangMills.Construction.InfiniteLattice.StatesAtOneSpacing
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicGibbsStateSpace.ConditionalMeasurability
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.PeriodicGibbsStateSpace.DenseLocalFamily
variable {a : ℝ}
def BorelGeneratedByIntegrals (𝒟 : Set (GaugeField a → ℂ)) : Prop :=
  borel (BorelProb a) =
    ⨆ F ∈ 𝒟, MeasurableSpace.comap (fun ρ : BorelProb a => ρ.integral F) (borel ℂ)
def ObservableIntegralsMeasurable (a : ℝ) : Prop :=
  ∀ A : GaugeField a → ℂ, IsBoundedObservable A →
    Measurable[borel (BorelProb a)] (fun ρ : BorelProb a => ρ.integral A)
def PreimagesShiftInvariant (κ : GaugeField a → GaugeFieldProbability a) :
    Prop :=
  ∀ E : Set (BorelProb a), MeasurableSet[borel (BorelProb a)] E →
    MeasurableSet[shiftInvariantSigma a] ((fun U => (κ U : BorelProb a)) ⁻¹' E)
def ExistenceAndMeasurability : Prop :=
  ∀ (D : Params) (ν : Measure (GaugeField D.mesh)), ν ∈ periodicGibbsSet D.L (D.K : ℕ) D.β →
    ∀ 𝒟 : Set (GaugeField D.mesh → ℂ), IsCountableRealDense 𝒟 →
      (∃ κ, IsRegularConditionalByIntegrals ν κ) ∧
      (SecondCountableTopology (BorelProb D.mesh) ∧ BorelGeneratedByIntegrals 𝒟 ∧
        ObservableIntegralsMeasurable D.mesh ∧
        ∀ κ, IsRegularConditionalByIntegrals ν κ →
          PreimagesShiftInvariant κ) ∧
      ∀ κ κ', IsRegularConditionalByIntegrals ν κ →
        IsRegularConditionalByIntegrals ν κ' →
          (∀ᵐ U ∂ν, κ U = κ' U) ∧ disintegrationImage ν κ = disintegrationImage ν κ'
end YangMills.Construction.PeriodicGibbsStateSpace.ConditionalMeasurability
