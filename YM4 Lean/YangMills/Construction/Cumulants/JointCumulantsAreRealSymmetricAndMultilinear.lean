import YangMills.Construction.Cumulants.JointCumulantsOfBoundedRealVariables
import YangMills.Construction.InfiniteLattice.MomentCumulantFormulaAndMultilinearForms
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants.RealSymmetricMultilinear
open Probability (IsBoundedRealRV)
open RealVariables (realPartialDerivOverFinset)
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
def logMgfReal (ν : Measure Ω) (X : Fin n → Ω → ℝ) : (Fin n → ℝ) → ℝ :=
  fun t => Real.log (momentGeneratingFunction ν X fun i => (t i : ℂ)).re
structure MgfAndLogProperties (ν : Measure Ω) (X : Fin n → Ω → ℝ) : Prop where
  integrable : ∀ t : Coordinates.ComplexCoordinates n,
    Integrable (fun ω => Complex.exp (∑ i, t i * (X i ω : ℂ))) ν
  holomorphic : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) Set.univ
    fun t _ => momentGeneratingFunction ν X t
  eq_one_at_zero : momentGeneratingFunction ν X 0 = 1
  pos_on_realLocus : ∀ t ∈ Coordinates.ComplexCoordinates.realLocus n,
    (momentGeneratingFunction ν X t).im = 0 ∧ 0 < (momentGeneratingFunction ν X t).re
  contDiff_log : ContDiff ℝ (⊤ : ℕ∞) (logMgfReal ν X)
  mixedCumulant_eq : mixedCumulant ν X =
    ((realPartialDerivOverFinset Finset.univ (logMgfReal ν X) 0 : ℝ) : ℂ)
def CumulantIsRealSymmetricMultilinear : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ), 1 ≤ n →
    (∀ X : Fin n → Ω → ℝ, (∀ i, IsBoundedRealRV (X i)) →
      MgfAndLogProperties ν X) ∧
    MultilinearForms.IsRealSymmetricForm
      {x : Ω → ℝ | IsBoundedRealRV x} (mixedCumulant (n := n) ν)
end YangMills.Construction.Cumulants.RealSymmetricMultilinear
