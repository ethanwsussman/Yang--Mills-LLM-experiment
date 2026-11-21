import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators PeriodicOperators.LogDetSecondDerivs
open Tower.ResponseOperators (ClassFnEqForm)
open LocalKernels.Periodisation (periodSide)
structure LocalLogDetTerm (L k : ℕ) where
  idx : PeriodicData
  op : ((colourEdges L k 0).Carrier → ℂ) → idx.Carrier → idx.Carrier → ℂ
  coeff : ℝ
structure LocalLogDetTerm.IsAdmissible {L k : ℕ} (D : LocalLogDetTerm L k) : Prop where
  periodic : IsPeriodic D.idx
  local_op : IsLocalOpFun (colourEdges L k 0) D.idx D.idx D.op
  symbol_isUnit : ∀ θ : InfiniteLattice.AmbientSpace,
    IsUnit (symbolHom D.idx D.idx (coeffZero (colourEdges L k 0) D.idx D.idx D.op)
      (toComplexVec θ) : Module.End ℂ (D.idx.UnitQuot → ℂ))
  real_on_real : IsRealOnRealFields (colourEdges L k 0) D.idx D.op
def LocalLogDetTerm.eval {L k : ℕ} (D : LocalLogDetTerm L k) (s : ℕ)
    (g : (colourEdges L k 0).QuotMod s → ℝ) : ℝ :=
  D.coeff * Real.log ‖LinearMap.det (quotOperator (colourEdges L k 0) D.idx D.op s
    fun c => (g c : ℂ))‖
def DifferenceIsLocalLogDetSum : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ Ds : List (LocalLogDetTerm L k), (∀ D ∈ Ds, D.IsAdmissible) ∧
      ∀ᶠ n in atTop, ∃ c ε : ℝ, 0 < ε ∧ ∀ (r : edgeFormSpace L n k 0)
        (g : (colourEdges L k 0).QuotMod (periodSide L n) → ℝ),
        ClassFnEqForm L n k 0 (restrictToPositiveEdges (r : Edge L n k 0 → Matrices.ComplexMatrix2))
          (fun x => (g x : ℂ)) →
        (∀ x, |g x| < ε) →
        chainMinusBackground a (PeriodicLattice.expTwist (r : Edge L n k 0 → Matrices.ComplexMatrix2)
            (trivialField L n k 0)) =
          (Ds.map fun D => D.eval (periodSide L n) g).sum + c
end YangMills.Construction.RunningCouplingSlope
end
