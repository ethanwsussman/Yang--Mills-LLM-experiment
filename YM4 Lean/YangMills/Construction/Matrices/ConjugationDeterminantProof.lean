import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfG
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.Matrices.ConjugationDeterminant
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
private def pauliMatrix : Fin 3 → ComplexMatrix2 :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]
private def pauliCoord (X : ComplexMatrix2) : Fin 3 → ℂ :=
  ![(X 0 1 + X 1 0) / 2, Complex.I * (X 0 1 - X 1 0) / 2, X 0 0]
private theorem pauliMatrix_mem_traceless (i : Fin 3) : pauliMatrix i ∈ traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem pauliMatrix_mem_hermitianTraceless (i : Fin 3) :
    pauliMatrix i ∈ hermitianTraceless := by apply _root_.YangMills.Construction.Matrices.PowerExpCharts.pauliFamily_mem_hermitianTraceless <;> assumption
private theorem sum_pauliCoord_smul (X : ComplexMatrix2) (hX : Matrix.trace X = 0) :
    ∑ i, pauliCoord X i • pauliMatrix i = X := by
  have h11 : X 1 1 = -X 0 0 := by
    rw [Matrix.trace_fin_two] at hX
    linear_combination hX
  have hI := Complex.I_mul_I
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_three, pauliCoord, pauliMatrix, Matrix.add_apply, h11]
  · linear_combination (-(X 0 1 - X 1 0) / 2) * hI
  · linear_combination ((X 0 1 - X 1 0) / 2) * hI
private theorem pauliCoord_sum (y : Fin 3 → ℂ) :
    pauliCoord (∑ i, y i • pauliMatrix i) = y := by
  have hI := Complex.I_mul_I
  funext i
  fin_cases i <;>
    simp [Fin.sum_univ_three, pauliCoord, pauliMatrix, Matrix.add_apply]
  · ring
  · linear_combination (-y 1) * hI
private theorem pauliCoord_add (X Y : ComplexMatrix2) :
    pauliCoord (X + Y) = pauliCoord X + pauliCoord Y := by
  funext i
  fin_cases i <;> simp [pauliCoord, Matrix.add_apply] <;> ring
private theorem pauliCoord_smul (c : ℂ) (X : ComplexMatrix2) :
    pauliCoord (c • X) = c • pauliCoord X := by
  funext i
  fin_cases i <;> simp [pauliCoord, Matrix.smul_apply] <;> ring
private theorem pauliCoord_real {X : ComplexMatrix2} (hX : X ∈ hermitianTraceless) (i : Fin 3) :
    (((pauliCoord X i).re : ℝ) : ℂ) = pauliCoord X i := by
  have h01 : X 0 1 = star (X 1 0) := congrFun (congrFun hX.1 0) 1
  have h10 : X 1 0 = star (X 0 1) := congrFun (congrFun hX.1 1) 0
  have h00 : X 0 0 = star (X 0 0) := congrFun (congrFun hX.1 0) 0
  rw [← Complex.conj_eq_iff_re]
  change star (pauliCoord X i) = pauliCoord X i
  fin_cases i
  · simp only [pauliCoord]
    simp [← h01, ← h10, add_comm]
  · simp only [pauliCoord]
    simp [← h01, ← h10]
    ring
  · simpa [pauliCoord] using h00.symm
private def pauliEquivComplex : traceless ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun X := pauliCoord X
  map_add' X Y := pauliCoord_add X Y
  map_smul' c X := pauliCoord_smul c X
  invFun y := ⟨∑ i, y i • pauliMatrix i,
    traceless.sum_mem fun i _ => traceless.smul_mem _ (pauliMatrix_mem_traceless i)⟩
  left_inv X := Subtype.ext (sum_pauliCoord_smul X X.2)
  right_inv y := pauliCoord_sum y
private theorem sum_real_smul_pauliMatrix (y : Fin 3 → ℝ) :
    ∑ i, y i • pauliMatrix i = ∑ i, ((y i : ℝ) : ℂ) • pauliMatrix i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a b
  simp
private def pauliEquivReal : hermitianTraceless ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun X i := (pauliCoord X i).re
  map_add' X Y := by
    funext i
    simp [pauliCoord_add]
  map_smul' c X := by
    funext i
    have h : pauliCoord (c • (X : ComplexMatrix2)) = (c : ℂ) • pauliCoord X := by
      rw [← pauliCoord_smul]
      congr 1
    simp [h]
  invFun y := ⟨∑ i, y i • pauliMatrix i,
    hermitianTraceless.sum_mem fun i _ =>
      hermitianTraceless.smul_mem _ (pauliMatrix_mem_hermitianTraceless i)⟩
  left_inv X := by
    apply Subtype.ext
    change ∑ i, (pauliCoord X i).re • pauliMatrix i = X
    rw [sum_real_smul_pauliMatrix]
    simp only [pauliCoord_real X.2]
    exact sum_pauliCoord_smul X X.2.2
  right_inv y := by
    funext i
    change (pauliCoord (∑ i, y i • pauliMatrix i) i).re = y i
    rw [sum_real_smul_pauliMatrix, pauliCoord_sum]
    simp
private def pauliBasisComplex : Module.Basis (Fin 3) ℂ traceless :=
  Module.Basis.ofEquivFun pauliEquivComplex
private def pauliBasisReal : Module.Basis (Fin 3) ℝ hermitianTraceless :=
  Module.Basis.ofEquivFun pauliEquivReal
private theorem pauliBasisComplex_val (j : Fin 3) :
    ((pauliBasisComplex j : traceless) : ComplexMatrix2) = pauliMatrix j := by
  simp [pauliBasisComplex, pauliEquivComplex, Pi.single_apply, ite_smul]
private theorem pauliBasisReal_val (j : Fin 3) :
    ((pauliBasisReal j : hermitianTraceless) : ComplexMatrix2) = pauliMatrix j := by
  simp [pauliBasisReal, pauliEquivReal, Pi.single_apply, ite_smul]
private def conjugationMatrix (g : ComplexMatrix2) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => pauliCoord (conjugateBy g (pauliMatrix j)) i
private theorem det_conjugateOnTraceless (g : ComplexMatrix2) :
    LinearMap.det (conjugateOnTraceless g) = (conjugationMatrix g).det := by
  rw [← LinearMap.det_toMatrix pauliBasisComplex]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  change pauliCoord (conjugateBy g ((pauliBasisComplex j : traceless) : ComplexMatrix2)) i = _
  rw [pauliBasisComplex_val]
  rfl
private theorem det_conjugateOnHermitianTraceless (g : specialUnitary) :
    ((LinearMap.det (conjugateOnHermitianTraceless g) : ℝ) : ℂ) =
      (conjugationMatrix (g : ComplexMatrix2)).det := by
  have h := RingHom.map_det Complex.ofRealHom
    (LinearMap.toMatrix pauliBasisReal pauliBasisReal (conjugateOnHermitianTraceless g))
  rw [Complex.ofRealHom_eq_coe] at h
  rw [← LinearMap.det_toMatrix pauliBasisReal, h]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe]
  rw [LinearMap.toMatrix_apply]
  change (((pauliCoord (conjugateBy (g : ComplexMatrix2)
    ((pauliBasisReal j : hermitianTraceless) : ComplexMatrix2)) i).re : ℝ) : ℂ) = _
  rw [pauliBasisReal_val,
    pauliCoord_real (conjugateBy_mem_hermitianTraceless g.2 _ (pauliMatrix_mem_hermitianTraceless j))]
  rfl
private theorem sum_pauliCoord_mul (U V : ComplexMatrix2) (hU : Matrix.trace U = 0)
    (hV : Matrix.trace V = 0) :
    ∑ i, pauliCoord U i * pauliCoord V i = (1 / 2 : ℂ) * Matrix.trace (U * V) := by
  have hU' : U 1 1 = -U 0 0 := by
    rw [Matrix.trace_fin_two] at hU
    linear_combination hU
  have hV' : V 1 1 = -V 0 0 := by
    rw [Matrix.trace_fin_two] at hV
    linear_combination hV
  have hI := Complex.I_mul_I
  simp only [Fin.sum_univ_three, pauliCoord, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, hU', hV']
  simp
  linear_combination ((U 0 1 - U 1 0) * (V 0 1 - V 1 0) / 4) * hI
private theorem half_trace_pauliMatrix_mul (j k : Fin 3) :
    (1 / 2 : ℂ) * Matrix.trace (pauliMatrix j * pauliMatrix k) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) j k := by
  fin_cases j <;> fin_cases k <;> simp [pauliMatrix, Matrix.trace_fin_two]
  all_goals norm_num
private theorem trace_conjugateBy_mul {g : ComplexMatrix2} (hg : IsUnit g.det)
    (X Y : ComplexMatrix2) :
    Matrix.trace (conjugateBy g X * conjugateBy g Y) = Matrix.trace (X * Y) := by
  have h : conjugateBy g X * conjugateBy g Y = g * (X * Y) * g⁻¹ := by
    simp only [conjugateBy]
    calc g * X * g⁻¹ * (g * Y * g⁻¹) = g * X * (g⁻¹ * g) * Y * g⁻¹ := by
          simp only [mul_assoc]
      _ = g * (X * Y) * g⁻¹ := by
          rw [Matrix.nonsing_inv_mul g hg]
          simp only [mul_assoc, mul_one]
  rw [h, Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul g hg, one_mul]
private theorem conjugationMatrix_orthogonal {g : ComplexMatrix2} (hg : IsUnit g.det) :
    (conjugationMatrix g).transpose * conjugationMatrix g = 1 := by
  ext j k
  have hj : Matrix.trace (conjugateBy g (pauliMatrix j)) = 0 :=
    conjugateByLinear_mem_traceless g _ (pauliMatrix_mem_traceless j)
  have hk : Matrix.trace (conjugateBy g (pauliMatrix k)) = 0 :=
    conjugateByLinear_mem_traceless g _ (pauliMatrix_mem_traceless k)
  rw [Matrix.mul_apply, ← half_trace_pauliMatrix_mul, ← trace_conjugateBy_mul hg,
    ← sum_pauliCoord_mul _ _ hj hk]
  rfl
private theorem det_conjugationMatrix_eq_one_or {g : ComplexMatrix2} (hg : IsUnit g.det) :
    (conjugationMatrix g).det = 1 ∨ (conjugationMatrix g).det = -1 := by
  have h := congrArg Matrix.det (conjugationMatrix_orthogonal hg)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact mul_self_eq_one_iff.mp h
private theorem conjugateBy_conjugateBy_inv {g : ComplexMatrix2} (hg : IsUnit g.det)
    (X : ComplexMatrix2) : conjugateBy g (conjugateBy g⁻¹ X) = X := by
  simp only [conjugateBy, Matrix.nonsing_inv_nonsing_inv g hg]
  calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [mul_assoc]
    _ = X := by rw [Matrix.mul_nonsing_inv g hg, one_mul, mul_one]
abbrev _root_.YangMills.SharedProofs.p1183 := @conjugateBy_conjugateBy_inv
theorem conjugationDeterminant_holds : ConjugationDeterminant := by
  intro g hg
  refine ⟨?_, ?_, fun hs => ⟨?_, ?_⟩⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨X, hX, rfl⟩
      exact conjugateByLinear_mem_traceless g X hX
    · intro X hX
      exact ⟨conjugateBy g⁻¹ X, conjugateByLinear_mem_traceless g⁻¹ X hX,
        conjugateBy_conjugateBy_inv hg X⟩
  · rw [det_conjugateOnTraceless]
    exact det_conjugationMatrix_eq_one_or hg
  · apply Set.Subset.antisymm
    · rintro _ ⟨X, hX, rfl⟩
      exact conjugateBy_mem_hermitianTraceless hs X hX
    · intro X hX
      have hinv : g⁻¹ ∈ specialUnitary := by
        rw [inv_eq_star_of_mem_specialUnitary hs]
        obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hs
        refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Unitary.star_mem hu, ?_⟩
        simp [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hd]
      exact ⟨conjugateBy g⁻¹ X, conjugateBy_mem_hermitianTraceless hinv X hX,
        conjugateBy_conjugateBy_inv hg X⟩
  · rw [det_conjugateOnTraceless, det_conjugateOnHermitianTraceless]
end YangMills.Construction.Matrices.ComplexMatrix2
