import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.StatesAtOneSpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def DisintegrationPushforwardIdentity (μ : Measure (GaugeField a))
    (k : GaugeField a → GaugeFieldProbability a)
    (g : GaugeFieldProbability a → ℂ) : Prop :=
  Measurable[shiftInvariantSigma a] (fun U => g (k U)) ∧
    ∫ ρ, g ρ ∂(disintegrationImage μ k) = ∫ U, g (k U) ∂μ
def DisintegrationPushforwardIdentityENNReal (μ : Measure (GaugeField a))
    (k : GaugeField a → GaugeFieldProbability a)
    (g : GaugeFieldProbability a → ℝ≥0∞) : Prop :=
  Measurable[shiftInvariantSigma a] (fun U => g (k U)) ∧
    ∫⁻ ρ, g ρ ∂(disintegrationImage μ k) = ∫⁻ U, g (k U) ∂μ
structure DisintegrationImageProperties (μ : GaugeFieldProbability a)
    (k : GaugeField a → GaugeFieldProbability a) : Prop where
  preimage_measurableSet_invariant : ∀ E : Set (GaugeFieldProbability a), MeasurableSet E →
    MeasurableSet[shiftInvariantSigma a] {U | k U ∈ E}
  measurable_disintegration : Measurable k
  pushforward_of_bounded : ∀ g : GaugeFieldProbability a → ℂ, Measurable g →
    (∃ C : ℝ, ∀ ρ, ‖g ρ‖ ≤ C) → DisintegrationPushforwardIdentity μ.1 k g
  pushforward_of_ennreal : ∀ g : GaugeFieldProbability a → ℝ≥0∞, Measurable g →
    DisintegrationPushforwardIdentityENNReal μ.1 k g
  integral_expect_eq : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    ∫ ρ, ρ.expect F ∂(disintegrationImage μ.1 k) = μ.expect F
def DisintegrationFixesInvariantObservables (μ : GaugeFieldProbability a)
    (k : GaugeField a → GaugeFieldProbability a) : Prop :=
  ∀ J : GaugeField a → ℂ, IsBoundedObservable J → Measurable[shiftInvariantSigma a] J →
    ∀ᵐ U ∂μ.1, (k U).expect J = J U ∧
      (k U).expect (fun V => ((‖J V - J U‖ ^ 2 : ℝ) : ℂ)) = 0
def InvariantDisintegrationTheorem : Prop :=
  ∀ s : Conventions.StandingParameters,
    ∀ μ : GaugeFieldProbability (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)),
    IsShiftInvariant μ.1 →
      (∃ k, IsInvariantDisintegration μ.1 k) ∧
      ∀ k, IsInvariantDisintegration μ.1 k →
        DisintegrationImageProperties μ k ∧
          DisintegrationFixesInvariantObservables μ k
end YangMills.Construction.InfiniteLattice
