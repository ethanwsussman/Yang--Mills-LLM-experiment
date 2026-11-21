import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.QuadraticMeanApproximation
variable {a : ℝ}
def TendstoForMeasure (μ : BorelProb a) (Fn : ℕ → GaugeField a → ℂ)
    (F : GaugeField a → ℂ) : Prop :=
  haveI : IsProbabilityMeasure μ.1 := μ.2
  TendstoInL2 μ.1 Fn F
def LinkMeasurableApproximable (μ : BorelProb a) : Prop :=
  ∀ S : Set (Link a), S ⊆ positiveLinkSet a → ∀ F : GaugeField a → ℂ,
    Measurable[linkSigma S] F → (∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) →
      ∃ Fn : ℕ → GaugeField a → ℂ,
        (∀ n, 1 ≤ n → Continuous (Fn n) ∧
          ∃ W : Set (Link a), W.Finite ∧ W ⊆ S ∧ DependsOnlyOnLinks W (Fn n)) ∧
        TendstoForMeasure μ Fn F
def RegionMeasurableApproximable (μ : BorelProb a) : Prop :=
  ∀ R : Set AmbientSpace, ∀ F ∈ boundedMeasurableIn a R,
    ∃ Fn : ℕ → GaugeField a → ℂ,
      (∀ n, 1 ≤ n → Continuous (Fn n) ∧ Fn n ∈ locallyMeasurableIn a R ∧
        Fn n ∈ boundedMeasurableIn a R) ∧
      TendstoForMeasure μ Fn F
def Statement : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ μ : BorelProb a,
    LinkMeasurableApproximable μ ∧ RegionMeasurableApproximable μ
end YangMills.Construction.GibbsAtFixedSpacing.QuadraticMeanApproximation
