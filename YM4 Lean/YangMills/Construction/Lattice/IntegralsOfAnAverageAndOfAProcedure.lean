import YangMills.Construction.Lattice.GaugeConfigSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ConfigSpaces
open YangMills.Construction.PeriodicLattice.FaddeevPopov YangMills.Construction.BorelKernels
open scoped ENNReal
universe u
section Averaged
variable {L m K : ℕ} {𝔅 : Finset (GradedBond L m K)} {𝒴 : Type u} [MeasurableSpace 𝒴]
  {S : Finset (FourTorus L m)}
def IsGaugeAveragedMeasure (𝔪 : ConfigSpace 𝔅 𝒴 → Measure (SiteGaugeGroup S))
    (ν ν' : FiniteComplexMeasure (ConfigSpace 𝔅 𝒴)) : Prop :=
  ∀ F : ConfigSpace 𝔅 𝒴 → ℂ, IsBorelMeasurable F → (∃ C : ℝ, ∀ ξ, ‖F ξ‖ ≤ C) →
    ν'.integral F (ContinuousLinearMap.mul ℝ ℂ) =
      ν.integral (fun ξ => ∫ u, F (gaugeTransformedPoint ξ u) ∂𝔪 ξ) (ContinuousLinearMap.mul ℝ ℂ)
def gaugeAveragedMeasure (𝔪 : ConfigSpace 𝔅 𝒴 → Measure (SiteGaugeGroup S))
    (ν : FiniteComplexMeasure (ConfigSpace 𝔅 𝒴)) :
    FiniteComplexMeasure (ConfigSpace 𝔅 𝒴) :=
  Classical.epsilon (IsGaugeAveragedMeasure 𝔪 ν)
end Averaged
end YangMills.Construction.PeriodicLattice.ConfigSpaces
