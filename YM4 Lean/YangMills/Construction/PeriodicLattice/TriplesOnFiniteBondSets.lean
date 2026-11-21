import YangMills.Construction.OneLoop.Conventions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace OneLoop
def pauliCoordinateEquiv : Matrices.ComplexMatrix2.traceless ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun X := ![((X : Matrices.ComplexMatrix2) 0 1 + (X : Matrices.ComplexMatrix2) 1 0) / 2,
    ((X : Matrices.ComplexMatrix2) 1 0 - (X : Matrices.ComplexMatrix2) 0 1) / (2 * Complex.I),
    (X : Matrices.ComplexMatrix2) 0 0]
  map_add' X Y := by
    ext a
    fin_cases a <;> simp <;> ring
  map_smul' c X := by
    ext a
    fin_cases a <;> simp <;> ring
  invFun z := ⟨z 0 • pauliX + z 1 • pauliY + z 2 • pauliZ, by
    change Matrix.trace _ = 0
    simp [pauliX, pauliY, pauliZ, Matrix.trace_fin_two]⟩
  left_inv X := by
    have hsum : (X : Matrices.ComplexMatrix2) 0 0 + (X : Matrices.ComplexMatrix2) 1 1 = 0 := by
      have htr : Matrix.trace (X : Matrices.ComplexMatrix2) = 0 := X.2
      simpa [Matrix.trace_fin_two] using htr
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ]
    · field_simp
      ring
    · field_simp
      ring
    · linear_combination -hsum
  right_inv z := by
    ext a
    fin_cases a <;> simp [pauliX, pauliY, pauliZ] <;> field_simp <;> ring
def pauliBasis : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless :=
  Module.Basis.ofEquivFun pauliCoordinateEquiv
theorem pauliBasis_coe_eq :
    ((pauliBasis 0 : Matrices.ComplexMatrix2.traceless) : Matrices.ComplexMatrix2) = pauliX ∧
      ((pauliBasis 1 : Matrices.ComplexMatrix2.traceless) : Matrices.ComplexMatrix2) = pauliY ∧
      ((pauliBasis 2 : Matrices.ComplexMatrix2.traceless) : Matrices.ComplexMatrix2) = pauliZ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pauliBasis, pauliCoordinateEquiv]
end OneLoop
end YangMills.Construction
