import YangMills.Construction.OneLoop.Conventions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def pauliFamily : Fin 3 → ComplexMatrix2 :=
  ![OneLoop.pauliX, OneLoop.pauliY, OneLoop.pauliZ]
theorem pauliFamily_apply :
    pauliFamily 0 = !![0, 1; 1, 0] ∧ pauliFamily 1 = !![0, -Complex.I; Complex.I, 0] ∧
      pauliFamily 2 = !![1, 0; 0, -1] :=
  ⟨rfl, rfl, rfl⟩
theorem sum_smul_pauliFamily (x : Fin 3 → ℂ) :
    ∑ γ, x γ • pauliFamily γ =
      !![x 2, x 0 - Complex.I * x 1; x 0 + Complex.I * x 1, -x 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ] <;> ring
theorem existsUnique_traceless_eq_sum_pauliFamily {A : ComplexMatrix2} (hA : A ∈ traceless) :
    ∃! x : Fin 3 → ℂ, A = ∑ γ, x γ • pauliFamily γ := by
  have hdiag : A 1 1 = -A 0 0 := by
    have h : Matrix.trace A = 0 := hA
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  refine ⟨![(A 0 1 + A 1 0) / 2, (A 1 0 - A 0 1) / (2 * Complex.I), A 0 0], ?_, ?_⟩
  · beta_reduce
    rw [sum_smul_pauliFamily]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hdiag] <;> field_simp <;> ring
  · intro y hy
    rw [sum_smul_pauliFamily] at hy
    have e00 : A 0 0 = y 2 := by rw [hy]; simp
    have e01 : A 0 1 = y 0 - Complex.I * y 1 := by rw [hy]; simp
    have e10 : A 1 0 = y 0 + Complex.I * y 1 := by rw [hy]; simp
    ext γ
    fin_cases γ
    · simp [e01, e10]
    · simp [e01, e10]; field_simp; ring
    · simp [e00]
namespace LieElement
theorem existsUnique_toMatrix_eq_real_sum (X : LieElement) :
    ∃! x : Fin 3 → ℝ, X.toMatrix = ∑ α, (x α : ℂ) • pauliFamily α := by
  have hm : X.toMatrix ∈ traceless := X.2.2
  have hdiag : X.toMatrix 1 1 = -X.toMatrix 0 0 := by
    have h : Matrix.trace X.toMatrix = 0 := hm
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  have hoff : X.toMatrix 0 1 = star (X.toMatrix 1 0) := X.toMatrix_entry_swap 1 0
  have hre : X.toMatrix 0 0 = star (X.toMatrix 0 0) := X.toMatrix_entry_swap 0 0
  have him : (X.toMatrix 0 0).im = 0 := by
    have := congrArg Complex.im hre
    simp at this
    linarith
  have hx : X.toMatrix = ∑ α, (((![(X.toMatrix 1 0).re, (X.toMatrix 1 0).im,
      (X.toMatrix 0 0).re] : Fin 3 → ℝ) α : ℝ) : ℂ) • pauliFamily α := by
    rw [sum_smul_pauliFamily]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [hdiag, hoff, him]
  refine ⟨_, hx, ?_⟩
  intro y hy
  obtain ⟨x, -, hu⟩ := existsUnique_traceless_eq_sum_pauliFamily hm
  have e := (hu _ hy).trans (hu _ hx).symm
  ext α
  exact Complex.ofReal_injective (congrFun e α)
end LieElement
end YangMills.Construction.Matrices.ComplexMatrix2
end
