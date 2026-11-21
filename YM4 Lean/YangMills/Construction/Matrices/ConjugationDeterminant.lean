import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def conjugateByLinear (V : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun := conjugateBy V
  map_add' A B := by simp only [conjugateBy, mul_add, add_mul]
  map_smul' c A := by simp only [conjugateBy, RingHom.id_apply, mul_smul_comm, smul_mul_assoc]
theorem conjugateByLinear_mem_traceless (V : ComplexMatrix2) :
    ∀ A ∈ traceless, conjugateByLinear V A ∈ traceless := by
  intro A hA
  change Matrix.trace (V * A * V⁻¹) = 0
  have hA' : Matrix.trace A = 0 := hA
  by_cases hV : IsUnit V.det
  · rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul V hV, one_mul, hA']
  · rw [Matrix.nonsing_inv_apply_not_isUnit V hV]
    simp
def conjugateOnTraceless (g : ComplexMatrix2) : traceless →ₗ[ℂ] traceless :=
  (conjugateByLinear g).restrict (conjugateByLinear_mem_traceless g)
theorem inv_eq_star_of_mem_specialUnitary {g : ComplexMatrix2} (hg : g ∈ specialUnitary) :
    g⁻¹ = star g :=
  Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup hg))
theorem conjugateBy_mem_hermitianTraceless {g : ComplexMatrix2} (hg : g ∈ specialUnitary) :
    ∀ A ∈ hermitianTraceless, conjugateBy g A ∈ hermitianTraceless := by
  rintro A ⟨hA, tA⟩
  refine ⟨?_, conjugateByLinear_mem_traceless g A tA⟩
  have hs : g⁻¹ = star g := inv_eq_star_of_mem_specialUnitary hg
  simp only [conjugateBy, hs, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, ← hA, mul_assoc]
def conjugateOnHermitianTraceless (g : specialUnitary) : hermitianTraceless →ₗ[ℝ] hermitianTraceless :=
  ((conjugateByLinear (g : ComplexMatrix2)).restrictScalars ℝ).restrict
    (conjugateBy_mem_hermitianTraceless g.2)
def ConjugationDeterminant : Prop :=
  ∀ g : ComplexMatrix2, IsUnit g.det →
    conjugateBy g '' (traceless : Set ComplexMatrix2) = traceless ∧
    (LinearMap.det (conjugateOnTraceless g) = 1 ∨ LinearMap.det (conjugateOnTraceless g) = -1) ∧
    ∀ hg : g ∈ specialUnitary, conjugateBy g '' (hermitianTraceless : Set ComplexMatrix2) = hermitianTraceless ∧
      ((LinearMap.det (conjugateOnHermitianTraceless ⟨g, hg⟩) : ℝ) : ℂ) = LinearMap.det (conjugateOnTraceless g)
end YangMills.Construction.Matrices.ComplexMatrix2
