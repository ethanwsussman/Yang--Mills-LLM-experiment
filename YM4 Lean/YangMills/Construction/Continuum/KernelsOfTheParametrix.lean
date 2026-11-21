import YangMills.Construction.TestFunctions.LaplacianOfR4
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Parametrix
open TorusMetric
def smoothStep (t : ℝ) : ℝ := if 0 < t then Real.exp (-1 / t) else 0
def shellCutoff (x : Fin 4 → ℝ) : ℝ :=
  smoothStep (2 - 4 * euclidNormVec x ^ 2) /
    (smoothStep (2 - 4 * euclidNormVec x ^ 2) + smoothStep (4 * euclidNormVec x ^ 2 - 1))
def logKernel (ε : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  if 0 < euclidNormVec x ^ 2 + ε then
    -(128 * Real.pi ^ 2)⁻¹ * (euclidNormVec x ^ 2 + ε) * Real.log (euclidNormVec x ^ 2 + ε)
  else 0
def innerKernelUnit (x : Fin 4 → ℝ) : ℝ := shellCutoff x * logKernel 0 x
def outerLogKernel (x : Fin 4 → ℝ) : ℝ := (1 - shellCutoff x) * logKernel 0 x
def outerKernelUnit : (Fin 4 → ℝ) → ℝ := TestFunctions.laplacianR4^[3] outerLogKernel
end Parametrix
end YangMills.Construction
