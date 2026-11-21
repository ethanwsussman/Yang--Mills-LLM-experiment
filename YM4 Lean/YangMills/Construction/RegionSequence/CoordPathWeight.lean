import YangMills.Construction.Dirichlet.CollarGeometry
import YangMills.Construction.RegionSequence.PastLastLevel
import YangMills.Construction.RegionSequence.SeparatedNestedRegions
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.RegionSequence
def lOneDist (p p' : Fin 4 → ℝ) : ℝ := ∑ μ, |p μ - p' μ|
end YangMills.Construction.RegionSequence
