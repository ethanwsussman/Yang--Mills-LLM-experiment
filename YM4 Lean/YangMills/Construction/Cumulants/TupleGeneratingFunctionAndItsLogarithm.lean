import YangMills.Construction.Cumulants.LogMomentGeneratingFunction
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace Cumulants
namespace TupleLogMGF
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def iteratedRealPartial (l : List (Fin n)) (φ : Coordinates.ComplexCoordinates n → ℂ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  l.foldr ComplexVariables.realPartialDeriv φ
def HasIteratedRealPartial (V : Set (Coordinates.ComplexCoordinates n)) :
    List (Fin n) → (Coordinates.ComplexCoordinates n → ℂ) → Prop
  | [], _ => Matrices.ComplexMatrix2.IsRelativelyOpen
      (Coordinates.ComplexCoordinates.realLocus n) V
  | i :: l, φ => HasIteratedRealPartial V l φ ∧
      ComplexVariables.HasRealPartialDeriv V (iteratedRealPartial l φ) i
def realLogTupleMGF (μ : Measure Ω) (X : Fin n → Ω → ℝ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  fun t => ((Real.log (tupleMomentGeneratingFunction μ X t).re : ℝ) : ℂ)
structure MGFEntireWithMoments (μ : Measure Ω) (X : Fin n → Ω → ℝ) : Prop where
  entire : ComplexVariables.IsEntireFun (tupleMomentGeneratingFunction μ X)
  apply_zero : tupleMomentGeneratingFunction μ X 0 = 1
  hasPartial : ∀ S : Finset (Fin n),
    ComplexVariables.HasPartialOverFinset univ S (tupleMomentGeneratingFunction μ X)
  partial_apply_zero : ∀ S : Finset (Fin n),
    ComplexVariables.partialOverFinset S (tupleMomentGeneratingFunction μ X) 0 =
      finsetMoment μ X S
structure LogMGFOnDomain (μ : Measure Ω) (X : Fin n → Ω → ℝ) : Prop where
  isOpen : IsOpen (logDomain μ X)
  zero_mem : (0 : Coordinates.ComplexCoordinates n) ∈ logDomain μ X
  holomorphic : ComplexVariables.IsHolomorphicScalar (logDomain μ X)
    (logMomentGeneratingFunction μ X)
  mgf_ne_zero : ∀ z ∈ logDomain μ X, tupleMomentGeneratingFunction μ X z ≠ 0
  exp_log : ∀ z ∈ logDomain μ X,
    Complex.exp (logMomentGeneratingFunction μ X z) = tupleMomentGeneratingFunction μ X z
  hasPartial : ∀ i : Fin n, ComplexVariables.HasPartialDeriv (logDomain μ X)
    (logMomentGeneratingFunction μ X) i
  partialDeriv_eq : ∀ (i : Fin n), ∀ z ∈ logDomain μ X,
    ComplexVariables.partialDeriv i (logMomentGeneratingFunction μ X) z =
      ComplexVariables.partialDeriv i (tupleMomentGeneratingFunction μ X) z /
        tupleMomentGeneratingFunction μ X z
  hasMixedPartial : ComplexVariables.HasPartialOverFinset (logDomain μ X) Finset.univ
    (logMomentGeneratingFunction μ X)
  mixedCumulant_eq : mixedCumulant μ X =
    ComplexVariables.partialOverFinset Finset.univ (logMomentGeneratingFunction μ X) 0
  apply_zero : logMomentGeneratingFunction μ X 0 = 0
structure CumulantViaRealLog (μ : Measure Ω) (X : Fin n → Ω → ℝ) : Prop where
  pos : ∀ t ∈ Coordinates.ComplexCoordinates.realLocus n,
    (tupleMomentGeneratingFunction μ X t).im = 0 ∧ 0 < (tupleMomentGeneratingFunction μ X t).re
  isRelativelyOpen : Matrices.ComplexMatrix2.IsRelativelyOpen
    (Coordinates.ComplexCoordinates.realLocus n)
    (logDomain μ X ∩ Coordinates.ComplexCoordinates.realLocus n)
  zero_mem : (0 : Coordinates.ComplexCoordinates n) ∈
    logDomain μ X ∩ Coordinates.ComplexCoordinates.realLocus n
  hasPartials : HasIteratedRealPartial
    (logDomain μ X ∩ Coordinates.ComplexCoordinates.realLocus n)
    (List.finRange n) (realLogTupleMGF μ X)
  mixedCumulant_eq : mixedCumulant μ X =
    iteratedRealPartial (List.finRange n) (realLogTupleMGF μ X) 0
structure FinsetCumulantsAsPartials (μ : Measure Ω) (X : Fin n → Ω → ℝ) : Prop where
  hasPartial : ∀ S : Finset (Fin n), S ≠ ∅ →
    ComplexVariables.HasPartialOverFinset (logDomain μ X) S (logMomentGeneratingFunction μ X)
  finsetCumulant_eq : ∀ S : Finset (Fin n), S ≠ ∅ →
    finsetCumulant μ X S = ComplexVariables.partialOverFinset S (logMomentGeneratingFunction μ X) 0
structure ShiftFormulas (μ : Measure Ω) (X : Fin n → Ω → ℝ) (a : Fin n → ℝ) : Prop where
  mgf_shift : ∀ z : Coordinates.ComplexCoordinates n,
    tupleMomentGeneratingFunction μ (shiftTuple X a) z =
      Complex.exp (realComplexPairing a z) * tupleMomentGeneratingFunction μ X z
  isOpen : IsOpen (logDomain μ X ∩ logDomain μ (shiftTuple X a))
  zero_mem : (0 : Coordinates.ComplexCoordinates n) ∈
    logDomain μ X ∩ logDomain μ (shiftTuple X a)
  hasPartial_shift : ∀ i : Fin n, ComplexVariables.HasPartialDeriv
    (logDomain μ X ∩ logDomain μ (shiftTuple X a))
    (logMomentGeneratingFunction μ (shiftTuple X a)) i
  hasPartial : ∀ i : Fin n, ComplexVariables.HasPartialDeriv
    (logDomain μ X ∩ logDomain μ (shiftTuple X a))
    (logMomentGeneratingFunction μ X) i
  partialDeriv_shift : ∀ (i : Fin n), ∀ z ∈ logDomain μ X ∩ logDomain μ (shiftTuple X a),
    ComplexVariables.partialDeriv i (logMomentGeneratingFunction μ (shiftTuple X a)) z =
      (a i : ℂ) + ComplexVariables.partialDeriv i (logMomentGeneratingFunction μ X) z
def TupleMGFAndLogTheorem : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin n → Ω → ℝ), 1 ≤ n → (∀ i, Probability.IsBoundedRealRV (X i)) →
    MGFEntireWithMoments μ X ∧ LogMGFOnDomain μ X ∧ CumulantViaRealLog μ X ∧
      FinsetCumulantsAsPartials μ X ∧ ∀ a : Fin n → ℝ, ShiftFormulas μ X a
end TupleLogMGF
end Cumulants
end YangMills.Construction
