import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def CovariantIteratesAtIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, 0 < k → j ≤ k →
    (∀ B ∈ edgeFormSpace (meshAt L k 0),
      complexIterDeriv L k j (fun _ => 1) B = linearSmoothingIter L k j B ∧
      iterCovariantDeriv L k (fun _ => 1) j B = crossingSmoothingIter L k j B ∧
      iterContourLogDrift L k (fun _ => 1) j B = cubeContourAverageIter L k j B) ∧
    ∀ l ∈ vertexFunctionSpace (meshAt L k 0),
      iterAdjointCubeAverage L k (fun _ => 1) j l = vertexSmoothingIter L k j l
end YangMills.Construction.Tower.FullSpace
end
