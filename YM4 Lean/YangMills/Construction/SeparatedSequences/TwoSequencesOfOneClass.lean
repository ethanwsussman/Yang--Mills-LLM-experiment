import YangMills.Construction.Lattice.SeparatedSequenceData
import YangMills.Construction.SeparatedSequences.ClassesFramesNormsAndKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses
abbrev ClassData.baseParamsAt (C : ClassData) (a : ℝ) (ha : 0 < a) :
    SeparatedSequences.BaseParameters where
  L := C.L
  odd_L := C.isAdmissible.1
  three_le_L := by
    have := C.isAdmissible.2
    omega
  K := C.cutoff
  K_pos := C.K.pos
  m := C.m
  m_pos := C.m.pos
  t := C.t
  t_le_K := C.t_le_cutoff
  blockExp := C.blockExp
  gapExp := C.gapExp
  L_le_pow_gapExp := C.L_le_pow_gapExp
  a := a
  a_pos := ha
end SeparatedClasses
end YangMills.Construction
end
