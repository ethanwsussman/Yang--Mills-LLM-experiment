import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def TrivialFieldSmoothingStep.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k i : ℕ, 0 < n → i < k →
    (∀ A ∈ Tower.edgeFormSpace L n k i,
      Tower.complexSmoothingDeriv (Tower.trivialField L n k i) A = Tower.linearSmoothing L n k i A ∧
      Tower.contourLogDrift (Tower.trivialField L n k i) A = Tower.cubeContourAverage L n k i A ∧
      Tower.covariantSmoothingDeriv (Tower.trivialField L n k i) A =
        Tower.crossingSmoothing L n k i A) ∧
    ∀ φ ∈ Tower.vertexFunctionSpace L n k i,
      Tower.adjointCubeAverage (Tower.trivialField L n k i) φ = Tower.vertexSmoothing L n k i φ
end Tower
end YangMills.Construction
end
