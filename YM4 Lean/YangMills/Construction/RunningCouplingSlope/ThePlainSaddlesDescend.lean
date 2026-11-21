import YangMills.Construction.RunningCouplingSlope.MixedSaddlesOfTheTop
import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
open Tower.ResponseOperators (ClassFnEqForm)
open LocalKernels.Periodisation (periodSide)
def SaddleKernelsPeriodize : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ᶠ n in atTop,
    ∃ ε : ℝ, 0 < ε ∧ ∀ (ω : edgeFormSpace L n k 0)
      (g : (colourEdges L k 0).QuotMod (periodSide L n) → ℝ),
      ClassFnEqForm L n k 0 (restrictToPositiveEdges (ω : Edge L n k 0 → Matrices.ComplexMatrix2))
        (fun x => (g x : ℂ)) →
      (∀ x, |g x| < ε) →
      PeriodizesTo (FullLattice.edgeSaddleOfForm a L k) (edgeIndexProj L n k)
        (saddleMatrix a (PeriodicLattice.expTwist (ω : Edge L n k 0 → Matrices.ComplexMatrix2)
          (trivialField L n k 0))) (periodSide L n) (fun x => (g x : ℂ)) ∧
      PeriodizesTo (FullLattice.vertexSaddleOfForm L k) (ghostIndexProj L n k)
        (ghostMatrix (PeriodicLattice.expTwist (ω : Edge L n k 0 → Matrices.ComplexMatrix2)
          (trivialField L n k 0))) (periodSide L n) (fun x => (g x : ℂ))
end YangMills.Construction.RunningCouplingSlope
end
