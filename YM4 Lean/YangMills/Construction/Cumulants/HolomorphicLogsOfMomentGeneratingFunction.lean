import YangMills.Construction.Cumulants.LogMomentGeneratingFunction
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.HolomorphicLog
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def weightedModulusSum (x : Fin n → Ω → ℝ) (z : Coordinates.ComplexCoordinates n) : ℝ :=
  ∑ i, ‖z i‖ * YangMills.Construction.Probability.supModulus fun ω => (x i ω : ℂ)
structure MomentGeneratingFunctionBound (ν : Measure Ω) (x : Fin n → Ω → ℝ) : Prop where
  norm_sub_one_le : ∀ z : Coordinates.ComplexCoordinates n,
    ‖tupleMomentGeneratingFunction ν x z - 1‖ ≤ Real.exp (weightedModulusSum x z) - 1
  subset_logDomain :
    {z : Coordinates.ComplexCoordinates n | weightedModulusSum x z < Real.log 2} ⊆ logDomain ν x
structure LogarithmRecoversCumulant (ν : Measure Ω) (x : Fin n → Ω → ℝ)
    (U' : Set (Coordinates.ComplexCoordinates n)) (L' : Coordinates.ComplexCoordinates n → ℂ) :
    Prop where
  eq_on_component : ∀ z ∈ connectedComponentIn (U' ∩ logDomain ν x) 0,
    L' z = logMomentGeneratingFunction ν x z
  hasPartialOverFinset : ComplexVariables.HasPartialOverFinset U' Finset.univ L'
  mixedPartial_eq : ComplexVariables.mixedPartialAtOrigin L' = mixedCumulant ν x
def HolomorphicLogsOfMomentGeneratingFunction : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ)
    (x : Fin n → Ω → ℝ), 1 ≤ n →
    (∀ i, YangMills.Construction.Probability.IsBoundedRealRV (x i)) →
    MomentGeneratingFunctionBound ν x ∧
      ∀ (U' : Set (Coordinates.ComplexCoordinates n)) (L' : Coordinates.ComplexCoordinates n → ℂ),
        IsOpen U' → (0 : Coordinates.ComplexCoordinates n) ∈ U' →
        ComplexVariables.IsHolomorphicScalar U' L' →
        (∀ z ∈ U', Complex.exp (L' z) = tupleMomentGeneratingFunction ν x z) → L' 0 = 0 →
        LogarithmRecoversCumulant ν x U' L'
end YangMills.Construction.Cumulants.HolomorphicLog
