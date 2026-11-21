import YangMills.Construction.SeparatedSequences.ClassesFramesNormsAndKernels
import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import YangMills.Construction.Torus.PhysicalTorusInLevelUnitsAsATorusOfGeneralSide
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice.DirichletOperators
noncomputable section
namespace SeparatedClasses
namespace ClassData
variable (C : ClassData)
abbrev levelUnitTorus : GeneralTorus.LevelUnitParams where
  L := C.L
  blocking := ⟨rfl, C.isAdmissible.1, C.isAdmissible.2⟩
  m := C.m
  m_pos := C.m.pos
  K := C.K
  K_pos := C.K.pos
  t := C.t
  t_le := C.t_le_cutoff
  blockExp := C.blockExp
  gapExp := C.gapExp
def scaleEquiv {S : ℝ} (hS : S ≠ 0) : C.Point ≃+ YangMills.Construction.Torus.PeriodicTorus 4 S :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle _ _ C.levelUnitTorus.physSide_ne_zero hS
variable {C}
abbrev regionEquiv (C : ClassData) (R : RegionSequence.NestedRegions) : C.Point ≃+ R.Point :=
  C.scaleEquiv R.side_pos.ne'
end ClassData
end SeparatedClasses
end
end YangMills.Construction
