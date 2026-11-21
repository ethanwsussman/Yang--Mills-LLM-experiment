import YangMills.Construction.InfiniteLattice.SeparatedLipschitzTuplesAndPartialFamilies
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.SeparatedFamilies
open YangMills.Construction.InfiniteLattice YangMills.Construction.CutoffLattice
structure TruncatedCorrelationWellDefined {L K : ℕ} (ν : Measure (FieldsAt L K)) (n : ℕ) :
    Prop where
  finite_support_faces : ∀ f ∈ boundedCompactlySupported,
    {p : ElementaryPlaquette (spacingAt L K) | f p.center ≠ 0}.Finite
  isBoundedRealRV : ∀ f ∈ boundedCompactlySupported,
    Probability.IsBoundedRealRV (smearedObservable L K f)
  logMGF_contDiffAt : ∀ f : Fin n → AmbientSpace → ℝ, (∀ i, f i ∈ boundedCompactlySupported) →
    ContDiffAt ℂ n (fun t => Complex.log (Cumulants.momentGeneratingFunction ν
      (fun i => smearedObservable L K (f i)) t)) 0
  eq_mixedCumulant : ∀ f : Fin n → AmbientSpace → ℝ, (∀ i, f i ∈ boundedCompactlySupported) →
    truncatedCorrelation ν f = Cumulants.mixedCumulant ν fun i => smearedObservable L K (f i)
  im_eq_zero : ∀ f : Fin n → AmbientSpace → ℝ, (∀ i, f i ∈ boundedCompactlySupported) →
    (truncatedCorrelation ν f).im = 0
  perm_invariant : ∀ f : Fin n → AmbientSpace → ℝ, (∀ i, f i ∈ boundedCompactlySupported) →
    ∀ σ : Equiv.Perm (Fin n), truncatedCorrelation ν (f ∘ σ) = truncatedCorrelation ν f
  slot_linear : ∀ f : Fin n → AmbientSpace → ℝ, (∀ i, f i ∈ boundedCompactlySupported) →
    ∀ (l : Fin n) (g g' : AmbientSpace → ℝ) (α α' : ℝ), g ∈ boundedCompactlySupported →
      g' ∈ boundedCompactlySupported →
      truncatedCorrelation ν (Function.update f l (α • g + α' • g')) =
        (α : ℂ) * truncatedCorrelation ν (Function.update f l g) +
          (α' : ℂ) * truncatedCorrelation ν (Function.update f l g')
def RadialFunctionalFamily.IsTruncatedFamilyOf {L K : ℕ} (Φ : RadialFunctionalFamily ⊤)
    (ν : Measure (FieldsAt L K)) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : separatedLipschitzSetIn n ⊤),
    (Φ.eval n hn X : ℂ) = truncatedCorrelationFamily ν n hn ⟨X.1, X.2.1⟩
def TruncatedCorrelationsOfProbabilityMeasures : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∃ V : Submodule ℝ (AmbientSpace → ℝ), (V : Set (AmbientSpace → ℝ)) = boundedCompactlySupported) ∧
    (∀ K : ℕ, 0 < K → ∀ ν ∈ fieldProbabilityMeasures L K, ∀ n : ℕ, 1 ≤ n →
      TruncatedCorrelationWellDefined ν n) ∧
    ∀ J₀ : Set ℕ, J₀.Infinite → (∀ j ∈ J₀, 0 < j) →
      ∀ (K : J₀ → ℕ) (ν : ∀ j, Measure (FieldsAt L (K j))), (∀ j, 0 < K j) →
        (∀ j, ν j ∈ fieldProbabilityMeasures L (K j)) →
        (∀ j, ∃ Φ : RadialFunctionalFamily ⊤, Φ.IsTruncatedFamilyOf (ν j)) ∧
        (∀ n : ℕ, separatedLipschitzSetIn n ⊤ = separatedLipschitzSet n) ∧
        Tendsto (fun _ : J₀ => (⊤ : ℝ≥0∞)) atTop (𝓝 ⊤)
end YangMills.Construction.SeparatedFamilies
