import YangMills.Construction.Cumulants.LogMomentGeneratingFunction
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.Cumulants.BoundedVariables
open Probability (IsBoundedRealRV)
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def logDomain (n : ℕ) (b : ℝ) : Set (Coordinates.ComplexCoordinates n) :=
  {t | ∑ i, ‖t i‖ < b⁻¹ * Real.log 2}
def expLinearCombination (x : Fin n → Ω → ℝ) (t : Coordinates.ComplexCoordinates n) : Ω → ℂ :=
  fun ω => Complex.exp (∑ i, t i * (x i ω : ℂ))
def monomialMulExp {k : ℕ} (x : Fin n → Ω → ℝ) (i : Fin k → Fin n)
    (t : Coordinates.ComplexCoordinates n) : Ω → ℂ :=
  fun ω => (∏ a, (x (i a) ω : ℂ)) * expLinearCombination x t ω
structure EntireWithIntegralDerivatives (ν : Measure Ω) (x : Fin n → Ω → ℝ) : Prop where
  integrable : ∀ t : Coordinates.ComplexCoordinates n, Integrable (expLinearCombination x t) ν
  entire : ComplexVariables.IsEntireFun (momentGeneratingFunction ν x)
  value_at_zero : momentGeneratingFunction ν x 0 = 1
  positive : ∀ t ∈ Coordinates.ComplexCoordinates.realLocus n,
    (momentGeneratingFunction ν x t).im = 0 ∧ 0 < (momentGeneratingFunction ν x t).re
  has_partials : ∀ (k : ℕ), 1 ≤ k → ∀ i : Fin k → Fin n,
    ComplexVariables.HasIteratedPartials univ (List.ofFn i) (momentGeneratingFunction ν x)
  integrable_under : ∀ (k : ℕ), 1 ≤ k → ∀ (i : Fin k → Fin n)
    (t : Coordinates.ComplexCoordinates n), Integrable (monomialMulExp x i t) ν
  under_integral : ∀ (k : ℕ), 1 ≤ k → ∀ (i : Fin k → Fin n)
    (t : Coordinates.ComplexCoordinates n),
    ComplexVariables.iteratedPartials (List.ofFn i) (momentGeneratingFunction ν x) t =
      ∫ ω, monomialMulExp x i t ω ∂ν
structure LogOnLogDomain (ν : Measure Ω) (x : Fin n → Ω → ℝ) (b : ℝ) : Prop where
  near_one : ∀ t ∈ logDomain n b, ‖momentGeneratingFunction ν x t - 1‖ < 1
  maps_to : MapsTo (momentGeneratingFunction ν x) (logDomain n b)
    ComplexVariables.nonpositiveRayComplement
  holomorphic : ComplexVariables.IsHolomorphicScalar (logDomain n b)
    (logMomentGeneratingFunction ν x)
  has_mixed_partial : ComplexVariables.HasPartialOverFinset (logDomain n b) Finset.univ
    (logMomentGeneratingFunction ν x)
  cumulant_eq : mixedCumulant ν x =
    ComplexVariables.mixedPartialAtOrigin (logMomentGeneratingFunction ν x)
  unique : ∀ (V : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ), Convex ℝ V → IsOpen V →
    (0 : Coordinates.ComplexCoordinates n) ∈ V → ContinuousOn F V → F 0 = 0 →
    (∀ t ∈ V, Complex.exp (F t) = momentGeneratingFunction ν x t) →
    ∀ t ∈ logDomain n b ∩ V, F t = logMomentGeneratingFunction ν x t
structure SubfamilyCumulants (ν : Measure Ω) (x : Fin n → Ω → ℝ) (b : ℝ) : Prop where
  has_partial : ∀ J : Finset (Fin n), J.Nonempty →
    ComplexVariables.HasPartialOverFinset (logDomain n b) J (logMomentGeneratingFunction ν x)
  cumulant_eq : ∀ J : Finset (Fin n), J.Nonempty →
    ComplexVariables.partialOverFinset J (logMomentGeneratingFunction ν x) 0 =
      finsetCumulant ν x J
structure CumulantRealSymmetric (ν : Measure Ω) (x : Fin n → Ω → ℝ) : Prop where
  real : (mixedCumulant ν x).im = 0
  symmetric : ∀ σ : Equiv.Perm (Fin n), mixedCumulant ν (fun i => x (σ i)) = mixedCumulant ν x
structure CumulantSpecialValues (ν : Measure Ω) (x : Fin n → Ω → ℝ) : Prop where
  mean : n = 1 → ∀ i, mixedCumulant ν x = ((∫ ω, x i ω ∂ν : ℝ) : ℂ)
  shift : 2 ≤ n → ∀ c : Fin n → ℝ, mixedCumulant ν (shiftTuple x c) = mixedCumulant ν x
  vanishes : ∀ i, x i = 0 → mixedCumulant ν x = 0
def BoundedGeneratingFunctionTheorem : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ)
    (x : Fin n → Ω → ℝ) (b : ℝ), 1 ≤ n → (∀ i, IsBoundedRealRV (x i)) → 0 < b →
    (∀ i ω, |x i ω| ≤ b) →
    EntireWithIntegralDerivatives ν x ∧ LogOnLogDomain ν x b ∧
      SubfamilyCumulants ν x b ∧ CumulantRealSymmetric ν x ∧ CumulantSpecialValues ν x
end YangMills.Construction.Cumulants.BoundedVariables
