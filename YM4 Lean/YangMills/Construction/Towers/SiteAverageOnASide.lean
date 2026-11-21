import YangMills.Construction.Towers.ExponentialConjugatesOfKernelsAndMaps
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.SideVertexSmoothing
def smoothingKernel (L n k i : ℕ) :
    PeriodicOperators.KernelMatrix (Fin 3 × Vertex L n k i) (Fin 3 × Vertex L n k (i + 1)) :=
  expConjOfMapAtZero (vertexCoordinate (Vertex L n k i))
    (vertexCoordinate (Vertex L n k (i + 1))) (vertexSmoothing L n k i)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k i : ℕ, 0 < n → i + 1 ≤ k →
    PeriodicOperators.OpNormSummable (meshWeight (meshAt L k i))
      (meshWeight (meshAt L k (i + 1))) Set.univ
      (PeriodicOperators.applyKernel (smoothingKernel L n k i)) ∧
    PeriodicOperators.wOpNorm (meshWeight (meshAt L k i))
      (meshWeight (meshAt L k (i + 1))) Set.univ
      (PeriodicOperators.applyKernel (smoothingKernel L n k i)) ≤
      ENNReal.ofReal 1
end YangMills.Construction.Tower.SideVertexSmoothing
end
