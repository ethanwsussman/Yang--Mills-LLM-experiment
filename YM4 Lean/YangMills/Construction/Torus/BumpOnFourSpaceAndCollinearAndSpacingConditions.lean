import YangMills.Construction.Torus.CollinearQuadruples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace QuadrupleClasses
def radialBumpR4 (x : Fin 4 → ℝ) : ℝ :=
  if euclidNormVec x ≤ 1 then (1 - euclidNormVec x ^ 2) ^ 2 else 0
def CollinearThetaCondition (θ : ℝ) : Prop := θ ≤ Collinear.collinearThetaBound
def SpacingCondition (t : ℝ) : Prop := 9 / 8 ≤ t ∧ t ≤ 49 / 24
end QuadrupleClasses
end YangMills.Construction
end
