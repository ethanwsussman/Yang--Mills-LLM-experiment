import YangMills.Construction.Conventions.PositiveConstant
import Mathlib
set_option autoImplicit false
open Filter Topology
universe u v
namespace YangMills.Construction.Conventions
def DependsOnlyOnQuantities {D : Type u} {Q : Type v} (quantities : D → Q) (x : D → ℝ) : Prop :=
  YangMills.Construction.Conventions.DependsOnlyThrough x quantities
end YangMills.Construction.Conventions
