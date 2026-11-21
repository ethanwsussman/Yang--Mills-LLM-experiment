import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LinearResponse
open TorusFields
def circleSub (N u v : ℝ) : ℝ := (u - v) - N * round ((u - v) / N)
def torusDisplacement {m : ℕ} (x y : TorusSite m) : Fin 4 → ℝ := fun i =>
  circleSub m ((y i).val : ℝ) ((x i).val : ℝ)
def plaquetteCentreDisplacement {N : ℕ} (p p' : TorusPlaquette N) : Fin 4 → ℝ := fun i =>
  torusDisplacement p.1 p'.1 i + ((if i = p'.2.1 then 1 else 0) + (if i = p'.2.2 then 1 else 0) -
    (if i = p.2.1 then 1 else 0) - (if i = p.2.2 then 1 else 0)) / 2
def sqNorm (z : Fin 4 → ℝ) : ℝ := ∑ i, z i ^ 2
def hyperplaneReflection (z : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  (if i = j then 1 else 0) - 2 * z i * z j / sqNorm z
def continuumCurvatureKernel (z : Fin 4 → ℝ) (μ ν ρ τ : Fin 4) : ℝ :=
  (hyperplaneReflection z μ ρ * hyperplaneReflection z ν τ - hyperplaneReflection z μ τ * hyperplaneReflection z ν ρ) /
    (Real.pi ^ 2 * sqNorm z ^ 2)
end LinearResponse
end YangMills.Construction
end
