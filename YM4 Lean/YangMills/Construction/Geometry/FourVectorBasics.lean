import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace FourVector
def unitVec (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ 1
def inner4 (v w : Fin 4 → ℝ) : ℝ := ∑ μ, v μ * w μ
def euclidNorm (v : Fin 4 → ℝ) : ℝ := Real.sqrt (inner4 v v)
theorem euclidNorm_eq_euclidNormVec (v : Fin 4 → ℝ) :
    euclidNorm v = YangMills.Construction.TorusMetric.euclidNormVec v := by
  simp [euclidNorm, inner4, YangMills.Construction.TorusMetric.euclidNormVec, pow_two]
def coordPartialDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Fin 4)
    (f : (Fin 4 → ℝ) → E) (x : Fin 4 → ℝ) : E :=
  lineDeriv ℝ f x (unitVec ν)
open Classical in
def propIndicator (P : Prop) : ℝ := if P then 1 else 0
def kronecker (ν ν' : Fin 4) : ℝ := propIndicator (ν = ν')
end FourVector
end YangMills.Construction
