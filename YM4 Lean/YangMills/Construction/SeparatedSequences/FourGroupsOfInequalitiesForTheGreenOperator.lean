import YangMills.Construction.Lattice.DirichletOperatorsOfASeparatedSequence
import YangMills.Construction.SeparatedSequences.ClassesFramesNormsAndKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses.ClassData
variable (C : ClassData)
def unitSpacingParameters : SeparatedSequences.BaseParameters where
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
  a := 1
  a_pos := one_pos
variable (Ω : ℕ → Set C.Point)
def greenOn (f : ↥(zeroFormsOn C.cutoff (Ω 0))) : C.SiteFn :=
  (C.unitSpacingParameters.zeroGreen Ω f).1
def greenOp (f : C.SiteFn) : C.SiteFn :=
  C.greenOn Ω ⟨siteProjection C.cutoff (Ω 0) f, LinearMap.mem_range_self _ _⟩
def greenDiv (g : C.BondFn) : C.SiteFn :=
  composeDiv Ω (C.greenOn Ω) g
variable {C Ω}
def expDecay (δ : ℝ) (y y' : C.Apex Ω) : ℝ :=
  Real.exp (-δ * (C.chainDist Ω y.point y'.point).toReal)
end SeparatedClasses.ClassData
end YangMills.Construction
end
