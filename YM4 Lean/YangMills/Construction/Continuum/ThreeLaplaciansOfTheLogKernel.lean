import YangMills.Construction.Continuum.KernelsOfTheParametrix
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Parametrix
open YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions
open scoped ContDiff
def TripleLaplacianLogKernel : Prop :=
  (∀ ε : ℝ, 0 ≤ ε →
    ContDiffOn ℝ ∞ (logKernel ε) {x | 0 < euclidNormVec x ^ 2 + ε} ∧
      ∀ x, 0 < euclidNormVec x ^ 2 + ε →
        laplacianR4^[3] (logKernel ε) x =
          12 * ε ^ 3 / Real.pi ^ 2 * (euclidNormVec x ^ 2 + ε) ^ (-5 : ℤ)) ∧
    ∀ x : Fin 4 → ℝ, x ≠ 0 → laplacianR4^[3] (logKernel 0) x = 0
end YangMills.Construction.Parametrix
