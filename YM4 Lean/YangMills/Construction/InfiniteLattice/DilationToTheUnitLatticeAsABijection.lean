import YangMills.Construction.InfiniteLattice.DictionaryBetweenSpacings
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
theorem pointToUnit_pointOfUnit (ha : 0 < a) (x : LatticePoint 1) :
    pointToUnit ha (pointOfUnit a x) = x :=
  Subtype.ext (inv_smul_smul₀ ha.ne' (x : AmbientSpace))
theorem pointOfUnit_pointToUnit (ha : 0 < a) (x : LatticePoint a) :
    pointOfUnit a (pointToUnit ha x) = x :=
  Subtype.ext (smul_inv_smul₀ ha.ne' (x : AmbientSpace))
def linkEquivUnit (ha : 0 < a) : Link 1 ≃ Link a where
  toFun := linkOfUnit a
  invFun := linkToUnit ha
  left_inv b := Link.ext (pointToUnit_pointOfUnit ha b.initial)
    (pointToUnit_pointOfUnit ha b.terminal)
  right_inv b := Link.ext (pointOfUnit_pointToUnit ha b.initial)
    (pointOfUnit_pointToUnit ha b.terminal)
def gaugeFieldEquivUnit (ha : 0 < a) : GaugeField a ≃ GaugeField 1 where
  toFun := gaugeFieldRescale a
  invFun := gaugeFieldUnrescale ha
  left_inv U := Subtype.ext (funext fun b =>
    congrArg U.1 ((linkEquivUnit ha).right_inv b))
  right_inv U := Subtype.ext (funext fun b =>
    congrArg U.1 ((linkEquivUnit ha).left_inv b))
def conjByScaling (ha : 0 < a) (r : AmbientSpace → AmbientSpace) : AmbientSpace → AmbientSpace :=
  inverseScaling ha ∘ r ∘ (inverseScaling ha).symm
end YangMills.Construction.InfiniteLattice
