import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RealityOfOneStep
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ V ∈ smallComplexFields L k j, V ∈ fieldSpace L k j →
      smoothingMap L k j V ∈ fieldSpace L k (j + 1) ∧
      (∀ (y : Vertex L k (j + 1)), ∀ x ∈ cubeVertices L (meshAt L k j) y,
        complexContourMean L V y x ∈ PeriodicLattice.compactGaugeGroup) ∧
      (∀ A ∈ edgeFormSpace (meshAt L k j),
        complexSmoothingDeriv V A ∈ edgeFormSpace (meshAt L k (j + 1))) ∧
      (∀ A ∈ edgeFormSpace (meshAt L k j),
        contourLogDrift V A ∈ vertexFunctionSpace (meshAt L k (j + 1))) ∧
      ∀ f ∈ vertexFunctionSpace (meshAt L k j),
        adjointCubeAverage V f ∈ vertexFunctionSpace (meshAt L k (j + 1))
end YangMills.Construction.Tower.FullSpace.RealityOfOneStep
end
