import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.RefinedLattices
import YangMills.Construction.InfiniteLattice.ReflectionFormOfAPeriodicGibbsState
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def LocalObsAboveIsAlgebra (t : halfSpacingTimes a) : Prop :=
  (0 : GaugeField a → ℂ) ∈ localObsAbove t ∧
  (∀ f ∈ localObsAbove t, ∀ f' ∈ localObsAbove t, f + f' ∈ localObsAbove t) ∧
  (∀ c : ℂ, ∀ f ∈ localObsAbove t, c • f ∈ localObsAbove t) ∧
  ∀ f ∈ localObsAbove t, ∀ f' ∈ localObsAbove t, f * f' ∈ localObsAbove t
def IsPosSemidefHermitianAbove (μ : MeasureTheory.Measure (GaugeField a))
    (t : halfSpacingTimes a) : Prop :=
  (∀ g ∈ localObsAbove t, ∀ f ∈ localObsAbove t, ∀ f' ∈ localObsAbove t, ∀ c c' : ℂ,
      reflectionForm μ t g (c • f + c' • f') =
        c * reflectionForm μ t g f + c' * reflectionForm μ t g f') ∧
  (∀ g ∈ localObsAbove t, ∀ g' ∈ localObsAbove t, ∀ f ∈ localObsAbove t, ∀ c c' : ℂ,
      reflectionForm μ t (c • g + c' • g') f =
        conj c * reflectionForm μ t g f + conj c' * reflectionForm μ t g' f) ∧
  (∀ g ∈ localObsAbove t, ∀ f ∈ localObsAbove t,
    reflectionForm μ t g f = conj (reflectionForm μ t f g)) ∧
  ∀ f ∈ localObsAbove t, ReflectionFormNonneg μ t f
def ReflectionFormPosAndSupBound : Prop :=
  ∀ s : Conventions.StandingParameters, ∀ β : ℝ, 0 < β → ∀ μ ∈ periodicGibbsSet s.L s.K β,
    ∀ t : halfSpacingTimes (refinedSpacing s.L s.K),
      LocalObsAboveIsAlgebra t ∧ IsPosSemidefHermitianAbove μ t ∧
        ∀ f ∈ localObsAbove t, reflectionSeminorm μ t f ≤ observableSupNorm f
end YangMills.Construction.InfiniteLattice
end
