import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace TorusCubes
def realCube (f : Fin 4 → ℝ) (t : ℝ) : Set (Fin 4 → ℝ) :=
  pi univ fun ν => Icc (f ν) (f ν + t)
def IsTorusCube (S t : ℝ) (X : Set (Torus4 S)) : Prop :=
  0 < t ∧ t < S ∧ ∃ f : Fin 4 → ℝ, X = torusProj S '' realCube f t
end TorusCubes
end YangMills.Construction
end
