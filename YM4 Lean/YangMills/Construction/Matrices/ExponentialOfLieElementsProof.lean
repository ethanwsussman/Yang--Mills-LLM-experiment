import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.ExponentialOfLieElements
import YangMills.Construction.Matrices.NormExpLogBasics
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2.LieExp
private theorem det_matExp_of_fullTrace_eq_zero (hlog : ExpLogEstimates) (Z : ComplexMatrix2)
    (hZ : fullTrace Z = 0) : (matExp Z).det = 1 := by
  have hdet : ∀ Z : ComplexMatrix2, (matExp Z).det = Complex.exp (fullTrace Z) :=
    hlog.2.2.2.2.2.1
  rw [hdet, hZ, Complex.exp_zero]
private theorem fullTrace_I_smul_eq_zero (A : ComplexMatrix2) (hA : fullTrace A = 0) :
    fullTrace (Complex.I • A) = 0 := by
  have hA' : Matrix.trace A = 0 := hA
  simp [fullTrace, Matrix.trace_smul, hA']
theorem expImaginaryLieMem_of_estimates (helem : NormExpLogBasics)
    (hlog : ExpLogEstimates) : ExpImaginaryLieMem := by
  refine ⟨fun Y hY => ?_, fun A hA => ?_⟩
  · have hY' : Y = Y.conjTranspose := hY.1
    have hstar : (Complex.I • Y).conjTranspose = -(Complex.I • Y) := by
      rw [Matrix.conjTranspose_smul, ← hY']
      simp
    have hfacts := helem.2.1 (Complex.I • Y)
    have hinv : matExp (Complex.I • Y) * matExp (-(Complex.I • Y)) = 1 := hfacts.2.2.1
    have hadj : (matExp (Complex.I • Y)).conjTranspose = matExp (-(Complex.I • Y)) := by
      rw [hfacts.2.2.2.2.2.1, hstar]
    refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨?_, ?_⟩
    · refine Matrix.mem_unitaryGroup_iff.2 ?_
      rw [Matrix.star_eq_conjTranspose, hadj]
      exact hinv
    · exact det_matExp_of_fullTrace_eq_zero hlog _ (fullTrace_I_smul_eq_zero Y hY.2)
  · exact det_matExp_of_fullTrace_eq_zero hlog _ (fullTrace_I_smul_eq_zero A hA)
end YangMills.Construction.Matrices.ComplexMatrix2.LieExp
