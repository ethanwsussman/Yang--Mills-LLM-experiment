import YangMills.Construction.Cumulants.JointCumulantsOfComplexVariables
import YangMills.Construction.Measures.ImageMeasuresAndJointLaws
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.BoundedComplexCumulants
def mgfNearOneSet {W : Type*} [MeasurableSpace W] (ν : Measure W) {n : ℕ} (Y : Fin n → W → ℂ) :
    Set (Coordinates.ComplexCoordinates n) :=
  {z | ‖complexMomentGeneratingFunction ν Y z - 1‖ < 1}
def CumulantProperties : Prop :=
  ∀ (W : Type) [MeasurableSpace W] (ν : Measure W) [IsProbabilityMeasure ν] (n : ℕ)
    (Y : Fin n → W → ℂ) (hY : ∀ i, IsBoundedComplexObservable (Y i)), 1 ≤ n →
    (Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) Set.univ
        (fun z _ => complexMomentGeneratingFunction ν Y z) ∧
      complexMomentGeneratingFunction ν Y 0 = 1 ∧
      IsOpen (mgfNearOneSet ν Y) ∧ (0 : Coordinates.ComplexCoordinates n) ∈ mgfNearOneSet ν Y ∧
      Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (mgfNearOneSet ν Y)
        (fun z _ => Complex.log (complexMomentGeneratingFunction ν Y z)) ∧
      HasComplexCumulant ν Y) ∧
    (∀ (ψ : W → W) (hψ : Measurable ψ), (∀ E, MeasurableSet E → ν (ψ ⁻¹' E) = ν E) →
      complexJointCumulant ν (fun i => Y i ∘ ψ) = complexJointCumulant ν Y ∧
      Measures.Pushforward.jointDistribution ν (fun i => Y i ∘ ψ) (fun i => (hY i).1.comp hψ) =
        Measures.Pushforward.jointDistribution ν Y (fun i => (hY i).1) ∧
      ∫ w, ∏ i, ((Y i ∘ ψ) w - ∫ w', (Y i ∘ ψ) w' ∂ν) ∂ν =
        ∫ w, ∏ i, (Y i w - ∫ w', Y i w' ∂ν) ∂ν) ∧
    (∀ (Q : ℕ) (X : Fin Q → W → ℂ) (l : Fin n → Fin Q → ℂ), 1 ≤ Q →
      (∀ q, IsBoundedComplexObservable (X q)) →
      (∀ i w, Y i w = ∑ q, l i q * X q w) →
      complexJointCumulant ν Y =
        ∑ r : Fin n → Fin Q, (∏ i, l i (r i)) * complexJointCumulant ν fun i => X (r i)) ∧
    (∀ ρ : Equiv.Perm (Fin n),
      complexJointCumulant ν (fun i => Y (ρ i)) = complexJointCumulant ν Y) ∧
    ∀ (i : Fin n) (l' l'' : ℂ) (Y' Y'' : W → ℂ), IsBoundedComplexObservable Y' →
      IsBoundedComplexObservable Y'' → (∀ w, Y i w = l' * Y' w + l'' * Y'' w) →
      complexJointCumulant ν Y =
        l' * complexJointCumulant ν (Function.update Y i Y') +
          l'' * complexJointCumulant ν (Function.update Y i Y'')
end YangMills.Construction.Cumulants.BoundedComplexCumulants
