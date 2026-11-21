import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open Classical
open MeasureTheory
def euclideanInner (u v : Fin 4 → ℝ) : ℝ := ∑ i, u i * v i
def fourPointKernelTraceStatement : Prop :=
  ∀ (z : Fin 4 → Fin 4 → ℝ) (e : Fin 4 → ℝ), YangMills.Construction.LinearResponse.sqNorm e = 1 →
    (∑ i, z i = 0) →
    (∀ i, 0 < YangMills.Construction.LinearResponse.sqNorm (z i)) →
    (∀ i, (1 - (1 / 8 : ℝ) ^ 2) * YangMills.Construction.LinearResponse.sqNorm (z i) ≤
      euclideanInner (z i) e ^ 2) →
    3 / Real.pi ^ 8 * ∏ i, (YangMills.Construction.LinearResponse.sqNorm (z i) ^ 2)⁻¹ ≤
        Matrix.trace (planeKernelMatrix (z 0) * planeKernelMatrix (z 1) * planeKernelMatrix (z 2) *
          planeKernelMatrix (z 3)) ∧
      Matrix.trace (planeKernelMatrix (z 0) * planeKernelMatrix (z 1) * planeKernelMatrix (z 2) *
          planeKernelMatrix (z 3)) ≤
        6 / Real.pi ^ 8 * ∏ i, (YangMills.Construction.LinearResponse.sqNorm (z i) ^ 2)⁻¹
end YangMills.Construction.ResponseInTheExpansion
end
