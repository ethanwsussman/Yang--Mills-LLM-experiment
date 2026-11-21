import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
noncomputable section
namespace YangMills.Construction.Tower
def CovariantIteratesAtTrivialField : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → 0 < k → j ≤ k →
    (∀ B ∈ edgeFormSpace L n k 0,
      complexIterDeriv L n k j (trivialField L n k 0) B =
        linearSmoothingIter L n k j B ∧
      iterCovariantDeriv L n k (trivialField L n k 0) j B =
        crossingSmoothingIter L n k j B ∧
      iterContourLogDrift L n k (trivialField L n k 0) j B =
        cubeContourAverageIter L n k j B) ∧
    ∀ l ∈ vertexFunctionSpace L n k 0,
      iterAdjointCubeAverage L n k (trivialField L n k 0) j l = vertexSmoothingIter L n k j l
end YangMills.Construction.Tower
end
