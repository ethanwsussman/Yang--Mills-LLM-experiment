import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def singleComplex (h : R4 → ℂ) : FreeSep := complexList fun _ : Fin 1 => h
structure IsStripHeight (c : ℝ) (F : FreeSep) (h : R4 → ℂ) (F' : FreeSep) : Prop where
  pos : 0 < c
  left_mem : F ∈ freeSpanIn {x | c < x 3}
  right_mem : F' ∈ freeSpanIn {x | c < x 3}
  mem_C1c : h ∈ C1c ℂ
  supp_subset : supp h ⊆ {x | |x 3| < c}
def stripInsertion (S : ConnFamily) (F : FreeSep) (h : R4 → ℂ) (F' : FreeSep) : ℂ :=
  centeredFnFree S (freeMul (freeMul (timeFlip.actFree (freeConj F)) (singleComplex h)) F')
end YangMills.Construction.EuclideanFunctionals
