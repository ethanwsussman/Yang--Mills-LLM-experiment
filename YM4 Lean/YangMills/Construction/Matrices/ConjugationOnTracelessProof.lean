import YangMills.Construction.Lattice.ComplexAverageAtAnImageBondProof
import YangMills.Construction.Matrices.ConjugationOnTraceless
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Matrices.ComplexMatrix2
private theorem isUnit_of_det_one {g : ComplexMatrix2} (h : g.det = 1) : IsUnit g := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.isUnit_of_det_eq_one <;> assumption
private theorem fullTrace_conj {g : ComplexMatrix2} (hg : IsUnit g) (X : ComplexMatrix2) :
    fullTrace (g * X * g⁻¹) = fullTrace X := by
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  simp only [fullTrace]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hdet, Matrix.one_mul]
private theorem conjugateBy_mem {g : ComplexMatrix2} (hg : IsUnit g) {X : ComplexMatrix2}
    (hX : X ∈ traceless) : conjugateBy g X ∈ traceless := by
  change fullTrace (g * X * g⁻¹) = 0
  rw [fullTrace_conj hg]
  exact hX
private theorem conjugateBy_inv_conjugateBy {g : ComplexMatrix2} (hg : IsUnit g)
    (X : ComplexMatrix2) : conjugateBy g⁻¹ (conjugateBy g X) = X := by
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  simp only [conjugateBy]
  rw [Matrix.nonsing_inv_nonsing_inv g hdet]
  calc g⁻¹ * (g * X * g⁻¹) * g = (g⁻¹ * g) * X * (g⁻¹ * g) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [Matrix.nonsing_inv_mul g hdet, Matrix.one_mul, Matrix.mul_one]
private theorem conjugateBy_conjugateBy_inv {g : ComplexMatrix2} (hg : IsUnit g)
    (X : ComplexMatrix2) : conjugateBy g (conjugateBy g⁻¹ X) = X := by
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  simp only [conjugateBy]
  rw [Matrix.nonsing_inv_nonsing_inv g hdet]
  calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [Matrix.mul_nonsing_inv g hdet, Matrix.one_mul, Matrix.mul_one]
theorem conjugation_preserves_traceless : ConjugationPreservesTraceless := by
  refine ⟨fun g hg => isUnit_of_det_one hg,
    fun g hg => isUnit_of_det_one (Matrix.mem_specialUnitaryGroup_iff.mp hg).2,
    fun g hg => ?_⟩
  have hinv : IsUnit g⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hg
  refine ⟨fun X => rfl, fullTrace_conj hg, fun X hX => ?_, fun X hX => conjugateBy_mem hg hX,
    ?_, ?_, ?_, ?_⟩
  · change fullTrace (g * X * g⁻¹) = 0
    rw [fullTrace_conj hg, hX]
  · intro z z' X _ X' _
    simp only [conjugateBy, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  · intro Y hY
    exact ⟨conjugateBy g⁻¹ Y, conjugateBy_mem hinv hY, conjugateBy_conjugateBy_inv hg Y⟩
  · intro X _ X' _ h
    rw [← conjugateBy_inv_conjugateBy hg X, h, conjugateBy_inv_conjugateBy hg X']
  · intro X _
    exact ⟨conjugateBy_inv_conjugateBy hg X, (conjugateBy_conjugateBy_inv hg X).symm⟩
end YangMills.Construction.Matrices.ComplexMatrix2
