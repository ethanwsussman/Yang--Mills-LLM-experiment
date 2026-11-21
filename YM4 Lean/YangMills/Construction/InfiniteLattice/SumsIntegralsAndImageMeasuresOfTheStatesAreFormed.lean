import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.WellDefinedStates
def SpecificationWellDefined (a β : ℝ) : Prop :=
  ∀ 𝓛 : Finset (Link a), (∀ b ∈ 𝓛, b.IsPositivelyOriented) →
    (facesTouching 𝓛).Finite ∧
      (∀ U : GaugeField a,
        0 < partitionFunction β 𝓛 U ∧ IsProbabilityMeasure (wilsonSpecification β 𝓛 U)) ∧
      exteriorSigma 𝓛 ≤ (inferInstance : MeasurableSpace (GaugeField a)) ∧
      Measurable (restrictTo 𝓛)
def ImagesOfBoundedObservables (a : ℝ) : Prop :=
  ∀ A : GaugeField a → ℂ, IsBoundedObservable A →
    (∀ s : LatticeSymmetry a, IsBoundedObservable (s.actOn A)) ∧
      ∀ P : LatticeMirror a, IsBoundedObservable fun U => A U * P.conjReflect A U
def ContinuousAreBoundedObservables (a : ℝ) : Prop :=
  ∀ A : GaugeField a → ℂ, Continuous A → IsBoundedObservable A
def Statement : Prop :=
  (∀ a : ℝ, 0 < a →
    (∀ β : ℝ, 0 < β → SpecificationWellDefined a β) ∧
      SmearedEnergyAndSymmetryAction.SmearedEnergyComplex a ∧
      SmearedEnergyAndSymmetryAction.SmearedEnergyReal a ∧
      ImagesOfBoundedObservables a ∧ ContinuousAreBoundedObservables a) ∧
    (∀ L K m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K → 0 < m → ∀ β : ℝ, 0 < β →
      IsProbabilityMeasure (liftedWilsonMeasure L m K β)) ∧
    ∀ (L m : ℕ) (j : ℤ), 0 < L → ∀ P : PeriodicMirror L m j, ∃ H, P.IsHalf H
end YangMills.Construction.InfiniteLattice.WellDefinedStates
