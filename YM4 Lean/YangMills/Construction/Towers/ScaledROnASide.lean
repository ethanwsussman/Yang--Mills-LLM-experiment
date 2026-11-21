import YangMills.Construction.Towers.ExponentialConjugatesOfKernelsAndMaps
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators (applyKernel wOpNorm OpNormSummable)
namespace RescaledRFiniteSide
def kernel (L n k : ℕ) :=
  expConjAtZero (rescaledOperators L n k (trivialField L n k 0)).R
def OpNormLeOne : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k : ℕ, 0 < n → 1 ≤ k →
    OpNormSummable (meshWeight (finestMesh L k))
      (meshWeight (meshAt L k k)) Set.univ (applyKernel (kernel L n k)) ∧
    wOpNorm (meshWeight (finestMesh L k))
      (meshWeight (meshAt L k k)) Set.univ (applyKernel (kernel L n k)) ≤
      ENNReal.ofReal 1
end RescaledRFiniteSide
end YangMills.Construction.Tower
end
