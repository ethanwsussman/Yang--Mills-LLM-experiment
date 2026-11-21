import YangMills.Construction.Lattice.SystemsOfRadiusInTheSettingOfTheTorusBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusBound.Setup.RadiusFamily
variable {D : YangMills.Construction.TorusBound.Setup} {ϱ' : ℝ} {hϱ' : 0 < ϱ'} (e : D.RadiusFamily ϱ' hϱ')
structure SatisfiesFiveBounds (Ce κe Eplus Clow : ℝ) : Prop where
  isLocal : e.Local
  analytic : e.Analytic
  expBounded : e.ExpBounded Ce κe
  upperStable : e.UpperStable Eplus
  floorBounded : e.FloorBounded Clow
end YangMills.Construction.TorusBound.Setup.RadiusFamily
end
