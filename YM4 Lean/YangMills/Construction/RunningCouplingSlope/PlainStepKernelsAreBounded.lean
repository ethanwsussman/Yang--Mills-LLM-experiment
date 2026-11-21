import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
def StepKernelNormBound : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n k : ℕ, 0 < n → 1 ≤ k →
    ∀ U : Edge L n k 0 → Matrices.ComplexMatrix2,
      (∀ j < k, meanIterate U j ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
        ∀ b, Matrices.ComplexMatrix2.operatorNorm (meanIterate U j b - 1) ≤ ρ) →
      ∀ j < k, ∀ [Fintype (Fin 3 × PositiveEdge L n k j)]
        [Fintype (Fin 3 × PositiveEdge L n k (j + 1))]
        [DecidableEq (Fin 3 × PositiveEdge L n k j)]
        [DecidableEq (Fin 3 × PositiveEdge L n k (j + 1))],
        ‖(Matrix.of (meanStepKernel L n k U j) :
          Matrix (Fin 3 × PositiveEdge L n k (j + 1)) (Fin 3 × PositiveEdge L n k j) ℂ)‖ ≤
          2 * ((L : ℝ) ^ 2)⁻¹
end YangMills.Construction.RunningCouplingSlope
end
