import YangMills.Construction.Cumulants.NonSingletonPartitions
import YangMills.Construction.Cumulants.LogMomentGeneratingFunction
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.RealVariables
open Probability (IsBoundedRealRV)
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def realPartialDeriv (j : Fin n) (F : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun t => fderiv ℝ F t (Pi.single j 1)
def iteratedRealPartialDeriv (l : List (Fin n)) (F : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  l.foldr realPartialDeriv F
def realPartialDerivOverFinset (J : Finset (Fin n)) (F : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  iteratedRealPartialDeriv J.sort F
def expLinearCombinationAt (ξ : Fin n → Ω → ℝ) (ω : Ω) : (Fin n → ℝ) → ℝ :=
  fun t => Real.exp (∑ i, t i * ξ i ω)
def realMomentGeneratingFunction (ν : Measure Ω) (ξ : Fin n → Ω → ℝ) : (Fin n → ℝ) → ℝ :=
  fun t => ∫ ω, expLinearCombinationAt ξ ω t ∂ν
def realLogMomentGeneratingFunction (ν : Measure Ω) (ξ : Fin n → Ω → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun t => Real.log (realMomentGeneratingFunction ν ξ t)
structure SmoothMomentGeneratingFunction (ν : Measure Ω) (ξ : Fin n → Ω → ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) (realMomentGeneratingFunction ν ξ)
  positive : ∀ t, 0 < realMomentGeneratingFunction ν ξ t
  integrable : ∀ (l : List (Fin n)) (t : Fin n → ℝ),
    Integrable (fun ω => iteratedRealPartialDeriv l (expLinearCombinationAt ξ ω) t) ν
  under_integral : ∀ (l : List (Fin n)) (t : Fin n → ℝ),
    iteratedRealPartialDeriv l (realMomentGeneratingFunction ν ξ) t =
      ∫ ω, iteratedRealPartialDeriv l (expLinearCombinationAt ξ ω) t ∂ν
  contDiff_log : ContDiff ℝ (⊤ : ℕ∞) (realLogMomentGeneratingFunction ν ξ)
  cumulant_eq : ∀ J : Finset (Fin n), J.Nonempty →
    finsetCumulant ν ξ J =
      ((realPartialDerivOverFinset J (realLogMomentGeneratingFunction ν ξ) 0 : ℝ) : ℂ)
  cumulant_real : (mixedCumulant ν ξ).im = 0
def BoundedRealCumulantTheorem : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ)
    (ξ : Fin n → Ω → ℝ), 1 ≤ n → (∀ i, IsBoundedRealRV (ξ i)) →
    SmoothMomentGeneratingFunction ν ξ ∧
    (∀ σ : Equiv.Perm (Fin n), mixedCumulant ν (fun i => ξ (σ i)) = mixedCumulant ν ξ) ∧
    (∀ (i₀ : Fin n) (η η' : Ω → ℝ) (α α' : ℝ), IsBoundedRealRV η →
      IsBoundedRealRV η' → (∀ ω, ξ i₀ ω = α * η ω + α' * η' ω) →
      mixedCumulant ν ξ =
        (α : ℂ) * mixedCumulant ν (Function.update ξ i₀ η) +
          (α' : ℂ) * mixedCumulant ν (Function.update ξ i₀ η')) ∧
    (2 ≤ n →
      ((∫ ω, ∏ i, (ξ i ω - ∫ ω', ξ i ω' ∂ν) ∂ν : ℝ) : ℂ) =
        ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts, finsetCumulant ν ξ J)
end YangMills.Construction.Cumulants.RealVariables
