import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.SmearedDensityAndConnectedFunctionsOfAMeasure
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.InfiniteLattice
open scoped Topology
namespace YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.Cumulants (mixedCumulant)
open YangMills.Construction.Probability (IsBoundedRealRV)
def CumulantsPolynomialInMomentsAndWeakLimits : Prop :=
  (∀ n : ℕ, 1 ≤ n → ∃ P : MvPolynomial {J : Finset (Fin n) // J.Nonempty} ℤ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : Fin n → Ω → ℝ), (∀ j, IsBoundedRealRV (X j)) →
      mixedCumulant μ X =
        MvPolynomial.aeval
          (fun J : {J : Finset (Fin n) // J.Nonempty} =>
            ((∫ ω, ∏ j ∈ J.1, X j ω ∂μ : ℝ) : ℂ)) P) ∧
  (∀ a : ℝ, 0 < a →
    (∀ f : AmbientSpace → ℂ, IsBoundedOfBoundedSupport f →
      {p : ElementaryPlaquette a | (fun U : GaugeField a =>
        f p.center * (faceEnergy U p : ℂ)) ≠ 0}.Finite ∧
      plaquetteSmearing f ∈ continuousLocal a ∧
      ((∀ x, (f x).im = 0) → ∀ U : GaugeField a, (plaquetteSmearing f U).im = 0)) ∧
    ∀ (μs : ℕ → BorelProb a) (μ : BorelProb a), BorelProb.TendstoWeak μs μ →
      (∀ (n : ℕ) (X : Fin n → GaugeField a → ℝ), 1 ≤ n → (∀ j, Continuous (X j)) →
        Tendsto (fun i => mixedCumulant (μs i).1 X) atTop (𝓝 (mixedCumulant μ.1 X))) ∧
      ∀ f : AmbientSpace → ℂ, IsBoundedOfBoundedSupport f →
        Tendsto (fun i => (μs i).integral (plaquetteSmearing f)) atTop
          (𝓝 (μ.integral (plaquetteSmearing f)))) ∧
  (∀ L K : ℕ, 0 < refinedSpacing L K →
    ∀ (μs : ℕ → BorelProb (refinedSpacing L K)) (μ : BorelProb (refinedSpacing L K)),
      BorelProb.TendstoWeak μs μ →
      ∀ (n : ℕ) (f : Fin n → AmbientSpace → ℝ), 2 ≤ n →
        (∀ j, IsBoundedBorelCompactlySupported (f j)) →
        Tendsto (fun i => ursellFunctionOfMeasure (L := L) (K := K) (μs i).1 f) atTop
          (𝓝 (ursellFunctionOfMeasure (L := L) (K := K) μ.1 f))) ∧
  (∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ'] (φ : Ω' → Ω), Measurable φ → μ = μ'.map φ →
    ∀ (n : ℕ) (X : Fin n → Ω → ℝ), 1 ≤ n → (∀ j, IsBoundedRealRV (X j)) →
      mixedCumulant μ X = mixedCumulant μ' fun j => X j ∘ φ)
end YangMills.Construction.GibbsAtFixedSpacing
