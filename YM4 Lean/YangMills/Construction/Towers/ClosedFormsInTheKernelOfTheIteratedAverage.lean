import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ClosedInSmoothingKernelIsExact : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ E ∈ edgeFormSpace L n k 0, IsClosedEdgeForm E → linearSmoothingIter L n k k E = 0 →
      E ∈ vertexCoboundary ''
        (vertexFunctionSpace L n k 0 : Set (Vertex L n k 0 → Matrices.ComplexMatrix2))
end YangMills.Construction.Tower
end
