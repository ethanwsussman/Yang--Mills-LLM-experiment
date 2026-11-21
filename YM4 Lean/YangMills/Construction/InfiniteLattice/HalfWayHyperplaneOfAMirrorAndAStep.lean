import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.InfiniteLattice.LatticeMirrorsGivenWithANormal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace NormalHyperplane
def midPlane (Q : NormalHyperplane) (h : Point) : NormalHyperplane :=
  ⟨Q.normal, Q.level + 1 / 2 * euclidDot Q.normal h, Q.normal_valid⟩
def IsOutwardNormalStep (Q : NormalHyperplane) (a : ℝ) (h : Point) : Prop :=
  h ∈ InfiniteLattice.latticeSubgroup a ∧ Q.reflectionLinear h = -h ∧ 0 < euclidDot Q.normal h
def IsMidPlaneOf (Q' : NormalHyperplane) (a : ℝ) (Q : NormalHyperplane) (h : Point) : Prop :=
  Q.IsLatticeMirror a ∧ Q.IsOutwardNormalStep a h ∧ Q' = Q.midPlane h
end NormalHyperplane
end LatticeConventions
end YangMills.Construction
end
