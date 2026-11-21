import YangMills.Construction.Towers.ExponentialConjugatesOfKernelsAndMaps
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.PeriodicOperators (KernelMatrix applyKernel wOpNorm OpNormSummable)
namespace CrossingSmoothingContraction
def crossingKernel (L m k i : ℕ) :
    KernelMatrix (Fin 3 × PositiveEdge L m k i) (Fin 3 × PositiveEdge L m k (i + 1)) :=
  expConjOfMapAtZero (edgePauliCoordinates L m k i) (edgePauliCoordinates L m k (i + 1))
    fun B => (L : ℝ)⁻¹ • crossingSmoothing L m k i B
def normAtMostOne : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k i : ℕ, 0 < m → i + 1 ≤ k →
    OpNormSummable (meshWeight (meshAt L k i))
      (meshWeight (meshAt L k (i + 1))) Set.univ (applyKernel (crossingKernel L m k i)) ∧
    wOpNorm (meshWeight (meshAt L k i))
      (meshWeight (meshAt L k (i + 1))) Set.univ (applyKernel (crossingKernel L m k i)) ≤
      ENNReal.ofReal 1
end CrossingSmoothingContraction
end YangMills.Construction.Tower
end
