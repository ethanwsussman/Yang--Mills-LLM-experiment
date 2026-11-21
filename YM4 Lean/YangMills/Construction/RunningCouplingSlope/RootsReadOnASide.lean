import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
def ResolventRootsPeriodize : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    IsEdgePeriodization L n k (FreeResolvents.edgeResolventSqrt L k) (periodicEdgeResolventSqrt L n k) ∧
    IsVertexPeriodization L n k (FreeResolvents.vertexResolventSqrt L k) (periodicVertexResolventSqrt L n k)
end YangMills.Construction.RunningCouplingSlope
end
