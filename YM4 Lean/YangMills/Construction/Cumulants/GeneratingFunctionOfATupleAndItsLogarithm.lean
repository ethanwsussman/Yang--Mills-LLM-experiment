import YangMills.Construction.Cumulants.DerivativesInDistinctVariablesAndTheLogarithmOfAGeneratingFunction
import YangMills.Construction.Cumulants.TupleGeneratingFunctionAndItsLogarithm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.RandomTuple.TupleLaplaceLog
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def realLogLaplace (ν : Measure Ω) (Y : Fin n → Ω → ℝ) : Coordinates.ComplexCoordinates n → ℂ :=
  fun t => ((Real.log (laplaceTransform ν Y t).re : ℝ) : ℂ)
structure EntireWithMomentDerivs (ν : Measure Ω) (Y : Fin n → Ω → ℝ) : Prop where
  entire : ComplexVariables.IsEntireFun (laplaceTransform ν Y)
  value_at_zero : laplaceTransform ν Y 0 = 1
  has_partial : ∀ B : Finset (Fin n),
    ComplexVariables.HasPartialOverFinset univ B (laplaceTransform ν Y)
  partial_at_zero : ∀ B : Finset (Fin n),
    ComplexVariables.partialOverFinset B (laplaceTransform ν Y) 0 =
      Probability.complexExpectation ν fun ω => ((∏ l ∈ B, Y l ω : ℝ) : ℂ)
structure LogLaplaceOnRegion (ν : Measure Ω) (Y : Fin n → Ω → ℝ) : Prop where
  isOpen : IsOpen (logRegion ν Y)
  zero_mem : (0 : Coordinates.ComplexCoordinates n) ∈ logRegion ν Y
  holomorphic : ComplexVariables.IsHolomorphicScalar (logRegion ν Y) (logLaplace ν Y)
  exp_eq : ∀ z ∈ logRegion ν Y, Complex.exp (logLaplace ν Y z) = laplaceTransform ν Y z
  has_partial : ∀ j : Fin n,
    ComplexVariables.HasPartialDeriv (logRegion ν Y) (logLaplace ν Y) j
  has_partial_generating : ∀ j : Fin n,
    ComplexVariables.HasPartialDeriv (logRegion ν Y) (laplaceTransform ν Y) j
  partial_eq : ∀ (j : Fin n), ∀ z ∈ logRegion ν Y,
    ComplexVariables.partialDeriv j (logLaplace ν Y) z =
      ComplexVariables.partialDeriv j (laplaceTransform ν Y) z / laplaceTransform ν Y z
  formed : ContDiffAt ℂ (n : WithTop ℕ∞)
    (fun t : Fin n → ℂ => Complex.log (Cumulants.momentGeneratingFunction ν Y t)) 0
  has_mixed_partial :
    ComplexVariables.HasPartialOverFinset (logRegion ν Y) Finset.univ (logLaplace ν Y)
  cumulant_eq : jointCumulant ν Y = ComplexVariables.partialOverFinset Finset.univ (logLaplace ν Y) 0
structure RealVariableCumulant (ν : Measure Ω) (Y : Fin n → Ω → ℝ) : Prop where
  joint_eq : Cumulants.mixedCumulant ν Y = jointCumulant ν Y
  positive : ∀ t ∈ Coordinates.ComplexCoordinates.realLocus n,
    (laplaceTransform ν Y t).im = 0 ∧ 0 < (laplaceTransform ν Y t).re
  zero_mem : (0 : Coordinates.ComplexCoordinates n) ∈
    logRegion ν Y ∩ Coordinates.ComplexCoordinates.realLocus n
  has_partials : Cumulants.TupleLogMGF.HasIteratedRealPartial
    (logRegion ν Y ∩ Coordinates.ComplexCoordinates.realLocus n) (List.finRange n)
    (realLogLaplace ν Y)
  cumulant_eq : jointCumulant ν Y =
    Cumulants.TupleLogMGF.iteratedRealPartial (List.finRange n) (realLogLaplace ν Y) 0
structure RestrictionCumulants (ν : Measure Ω) (Y : Fin n → Ω → ℝ) : Prop where
  has_partial : ∀ B : Finset (Fin n), B ≠ ∅ →
    ComplexVariables.HasPartialOverFinset (logRegion ν Y) B (logLaplace ν Y)
  cumulant_eq : ∀ B : Finset (Fin n), B ≠ ∅ →
    jointCumulant ν (restrictTo Y B) = ComplexVariables.partialOverFinset B (logLaplace ν Y) 0
structure TranslationDerivs (ν : Measure Ω) (Y : Fin n → Ω → ℝ) (c : Fin n → ℝ) : Prop where
  isOpen : IsOpen (logRegion ν Y ∩ logRegion ν (translate Y c))
  zero_mem : (0 : Coordinates.ComplexCoordinates n) ∈ logRegion ν Y ∩ logRegion ν (translate Y c)
  has_partial_shifted : ∀ j : Fin n, ComplexVariables.HasPartialDeriv
    (logRegion ν Y ∩ logRegion ν (translate Y c)) (logLaplace ν (translate Y c)) j
  has_partial : ∀ j : Fin n, ComplexVariables.HasPartialDeriv
    (logRegion ν Y ∩ logRegion ν (translate Y c)) (logLaplace ν Y) j
  partial_eq : ∀ (j : Fin n), ∀ z ∈ logRegion ν Y ∩ logRegion ν (translate Y c),
    ComplexVariables.partialDeriv j (logLaplace ν (translate Y c)) z =
      (c j : ℂ) + ComplexVariables.partialDeriv j (logLaplace ν Y) z
def LaplaceAndLogTheorem : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ)
    (Y : Fin n → Ω → ℝ), 1 ≤ n → (∀ i, Probability.IsBoundedRealRV (Y i)) →
    EntireWithMomentDerivs ν Y ∧ LogLaplaceOnRegion ν Y ∧ RealVariableCumulant ν Y ∧
      RestrictionCumulants ν Y ∧ ∀ c : Fin n → ℝ, TranslationDerivs ν Y c
end YangMills.Construction.RandomTuple.TupleLaplaceLog
