import YangMills.Construction.RunningCouplingSlope.FirstOrderOfTheLeastPoint
import YangMills.Construction.RunningCouplingSlope.SystemOfTheFirstOrder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
open Tower.CriticalBranchResponse
def FirstOrderSystemSolution : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (B : edgeFormSpace L n k k) (τ : LevelTriple L n k), SolvesFirstOrderSystem a B τ →
      τ.2.1 = linearConstraintAdjoint L n k τ.2.2 ∧
      (∀ i, τ.1.2 i = a⁻¹ • (linearConstraintAdjoint L n k τ.2.2).2 i) ∧
      ∃ (G : edgeFormSpace L n k k) (h : vertexFunctionSpace L n k 0),
        (G : Edge L n k k → Matrices.ComplexMatrix2) = linearChain (0, τ.1.2) k ∧
        (τ.2.2 : Edge L n k k → Matrices.ComplexMatrix2) =
          periodicDefect L n k ((B : Edge L n k k → Matrices.ComplexMatrix2) - G) ∧
        (τ.1.1 : Edge L n k 0 → Matrices.ComplexMatrix2) =
          (meshScaledResponse L n k ((B : Edge L n k k → Matrices.ComplexMatrix2) - G) : Edge L n k 0 → Matrices.ComplexMatrix2) +
            vertexCoboundary (h : Vertex L n k 0 → Matrices.ComplexMatrix2)
end YangMills.Construction.RunningCouplingSlope
end
