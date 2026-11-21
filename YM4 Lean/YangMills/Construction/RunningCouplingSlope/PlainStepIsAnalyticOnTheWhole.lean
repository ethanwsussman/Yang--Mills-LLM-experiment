import YangMills.Construction.RunningCouplingSlope.OnePlainStepOnTheWhole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
open YangMills.Construction.Tower YangMills.Construction.Tower.FullSpace
open scoped Topology Matrix.Norms.L2Operator
def MeanStepAnalytic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ δ : ℝ, 0 < δ ∧ ∀ k m : ℕ, m < k →
    ∀ (l : ℕ) (W : Coordinates.ComplexCoordinates l → FullSpace.Edge L k m → Matrices.ComplexMatrix2)
      (p : Coordinates.ComplexCoordinates l),
      (∀ b, AnalyticAt ℂ (fun w => W w b) p) →
      (∀ᶠ w in 𝓝 p, W w ∈ nearIdentityFields L k m δ) →
      (∀ c, AnalyticAt ℂ (fun w => nextMeanIterate (W w) c) p) ∧
      (∀ c : FullSpace.Edge L k (m + 1), c.IsPositivelyOriented →
        AnalyticAt ℂ (fun w => (meanRadius (W w) c)⁻¹) p) ∧
      (∀ B ∈ FullSpace.complexEdgeForms (meshAt L k m), ∀ c,
        AnalyticAt ℂ (fun w => meanCovariantStep (W w) B c) p) ∧
      ∀ (y : FullSpace.Vertex L k (m + 1)) (x : FullSpace.Vertex L k m),
        x ∈ FullSpace.cubeVertices L (meshAt L k m) y →
        AnalyticAt ℂ (fun w => FullSpace.complexContourMean L (W w) y x) p
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
