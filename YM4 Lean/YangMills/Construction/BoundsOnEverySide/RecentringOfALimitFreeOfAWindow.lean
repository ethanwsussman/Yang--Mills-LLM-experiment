import YangMills.Construction.BoundsOnEverySide.LimitsAlongStatesFreeOfAWindow
import YangMills.Construction.Continuum.SubTuplesIsometriesAndTheConjugateOnFourSpace
import YangMills.Construction.LimitsAlongPeriodicGibbsStates.TheLetterSForALimitAlongPeriodicGibbsStates
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.BoundsOnEverySide
def LimitRecentring.Statement : Prop :=
  ∀ (P : YangMills.Construction.Conventions.StandingParameters) (n : ℕ → ℕ) (g : ℕ → ℝ)
    (μ ω : ∀ j, Measure (YangMills.Construction.InfiniteLattice.GaugeField
      (YangMills.Construction.PeriodicLattice.meshSize P.L (n j : ℤ))))
    (σ : YangMills.Construction.R4TupleForms.FinTuple P → ℝ)
    (hσ : YangMills.Construction.PeriodicGibbsLimit.HasMultilinearConnected σ),
    YangMills.Construction.BoundsOnEverySide.IsPeriodicStateLimit n g μ ω σ →
    (∀ X : YangMills.Construction.R4TupleForms.FinTuple P,
      YangMills.Construction.PeriodicGibbsLimit.centredOfLimit σ hσ X =
        ∑ I : Finset (Fin (YangMills.Construction.Continuum.SeparatedFourTuples.tupleLength X)),
          σ (YangMills.Construction.Continuum.SeparatedFourTuples.sepSubTuple X I) *
            ∏ i ∈ Iᶜ, (-σ (YangMills.Construction.Continuum.SeparatedFourTuples.sepSubTuple X {i}))) ∧
    ∀ X : YangMills.Construction.R4TupleForms.FinTuple P,
      Tendsto (fun j => YangMills.Construction.StateLimits.pairedValue n μ μ j X) atTop
        (𝓝 (YangMills.Construction.PeriodicGibbsLimit.centredOfLimit σ hσ X))
end YangMills.Construction.BoundsOnEverySide
end
