import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import YangMills.Construction.Probability.BoundedComplexExpectation
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants
open YangMills.Construction.Probability (IsBoundedRealRV IsBoundedComplexRV supModulus
  complexExpectation)
open YangMills.Construction.ComplexVariables (expComp IsEntireFun IsHolomorphicScalar absMonomial
  IsAbsSummable indexSum logPrincipal nonpositiveRayComplement)
open YangMills.Construction.PowerSeries (MultiIndex)
open YangMills.Construction.Coordinates (ComplexCoordinates)
def ExponentialMomentSeriesExpansion : Prop :=
  ∀ (S : Type) [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ)
    (x : Fin n → S → ℝ), 1 ≤ n → (∀ i, IsBoundedRealRV (x i)) →
    let b : Fin n → ℝ := fun i => supModulus fun ω => (x i ω : ℂ)
    let e : ComplexCoordinates n → S → ℂ := fun z => expComp fun ω => ∑ i, z i * (x i ω : ℂ)
    let m : MultiIndex n → ℂ := fun α =>
      complexExpectation ν fun ω => ((MultiIndex.monomial x α ω : ℝ) : ℂ)
    let F : ComplexCoordinates n → ℂ := fun z => complexExpectation ν (e z)
    let U : Set (ComplexCoordinates n) := {z | ‖F z - 1‖ < 1}
    (∀ α : MultiIndex n, IsBoundedRealRV (MultiIndex.monomial x α) ∧
      supModulus (fun ω => ((MultiIndex.monomial x α ω : ℝ) : ℂ)) ≤ MultiIndex.monomial b α) ∧
    (∀ z : ComplexCoordinates n, IsBoundedComplexRV (e z) ∧
      ∀ ω, ‖e z ω‖ ≤ Real.exp (∑ i, ‖z i‖ * b i)) ∧
    (∀ (t : Fin n → ℝ) (ω : S), (e (fun i => (t i : ℂ)) ω).im = 0 ∧
      Real.exp (-∑ i, |t i| * b i) ≤ (e (fun i => (t i : ℂ)) ω).re) ∧
    (∀ z : ComplexCoordinates n,
      IsAbsSummable (fun α => MultiIndex.monomial z α / (MultiIndex.factorial α : ℂ) * m α) ∧
      F z = indexSum
        (fun α => MultiIndex.monomial z α / (MultiIndex.factorial α : ℂ) * m α) ∧
      (∀ α, ‖m α‖ ≤ MultiIndex.monomial b α) ∧
      HasSum (fun α : MultiIndex n =>
          absMonomial z α / (MultiIndex.factorial α : ℝ) * MultiIndex.monomial b α)
        (Real.exp (∑ i, ‖z i‖ * b i))) ∧
    IsEntireFun F ∧ F 0 = 1 ∧ IsOpen U ∧ (0 : ComplexCoordinates n) ∈ U ∧
    (∀ z ∈ U, F z ∈ nonpositiveRayComplement) ∧ IsHolomorphicScalar U (logPrincipal ∘ F)
end YangMills.Construction.Cumulants
