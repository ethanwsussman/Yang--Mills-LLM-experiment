import YangMills.Construction.Gaussian.KernelGaussianIntegral
import YangMills.Construction.Towers.TheSaddleDeterminant
import Mathlib
set_option autoImplicit false
open Matrix Module
noncomputable section
namespace YangMills.Construction.GaussianConstraint.SaddleDeterminant
section Blocks
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
theorem abs_det_fromBlocks_transpose_zero (D N : Matrix κ κ ℝ) :
    |(fromBlocks D Nᵀ N 0).det| = N.det ^ 2 := by
  set sw : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ := fromBlocks 0 1 1 0 with hsw
  have hs : sw.det ^ 2 = 1 := by
    rw [sq, ← det_mul, hsw, fromBlocks_multiply]
    simp
  have hm : fromBlocks D Nᵀ N 0 * sw = fromBlocks Nᵀ D 0 N := by
    rw [hsw, fromBlocks_multiply]
    simp
  have hd : (fromBlocks D Nᵀ N 0).det * sw.det = N.det ^ 2 := by
    rw [← det_mul, hm, det_fromBlocks_zero₂₁, det_transpose, sq]
  have habs : |sw.det| = 1 := by
    rw [← sq_eq_sq₀ (abs_nonneg _) zero_le_one, sq_abs, hs, one_pow]
  calc |(fromBlocks D Nᵀ N 0).det|
      = |(fromBlocks D Nᵀ N 0).det| * |sw.det| := by rw [habs, mul_one]
    _ = |N.det ^ 2| := by rw [← abs_mul, hd]
    _ = N.det ^ 2 := abs_of_nonneg (sq_nonneg _)
theorem abs_det_threeBlock (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix κ ι ℝ)
    (D N : Matrix κ κ ℝ) (hN : IsUnit N.det) :
    |(fromBlocks A (fromCols B 0) (fromRows C 0) (fromBlocks D Nᵀ N 0)).det| =
      |A.det| * N.det ^ 2 := by
  have hNt : IsUnit Nᵀ.det := by rwa [det_transpose]
  have hinv : Nᵀ * (Nᵀ)⁻¹ = 1 := mul_nonsing_inv _ hNt
  set G : Matrix (κ ⊕ κ) ι ℝ := fromRows 0 (-((Nᵀ)⁻¹ * C)) with hG
  have hBG : fromCols B (0 : Matrix ι κ ℝ) * G = 0 := by
    rw [hG, fromCols_mul_fromRows]
    simp
  have hDG : fromBlocks D Nᵀ N 0 * G = fromRows (-C) 0 := by
    rw [hG, fromBlocks_mul_fromRows]
    simp [← Matrix.mul_assoc, hinv]
  have hmul : fromBlocks A (fromCols B 0) (fromRows C 0) (fromBlocks D Nᵀ N 0) *
      fromBlocks 1 0 G 1 = fromBlocks A (fromCols B 0) 0 (fromBlocks D Nᵀ N 0) := by
    have hz : fromRows C 0 + fromRows (-C) 0 = (0 : Matrix (κ ⊕ κ) ι ℝ) := by
      ext i j
      rcases i with i | i <;> simp
    rw [fromBlocks_multiply, hBG, hDG]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, hz]
  have hdet := congrArg det hmul
  rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁] at hdet
  simp only [det_one, mul_one] at hdet
  rw [hdet, abs_mul, abs_det_fromBlocks_transpose_zero]
theorem abs_det_saddleMatrix (X : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (M : Matrix κ (ι ⊕ κ) ℝ)
    (hM : ∀ f i, M f (Sum.inl i) = 0) (hN : IsUnit M.toCols₂.det) :
    |(fromBlocks X Mᵀ M 0).det| = |X.toBlocks₁₁.det| * M.toCols₂.det ^ 2 := by
  have hre : (fromBlocks X Mᵀ M 0).submatrix (Equiv.sumAssoc ι κ κ).symm
      (Equiv.sumAssoc ι κ κ).symm =
      fromBlocks X.toBlocks₁₁ (fromCols X.toBlocks₁₂ 0) (fromRows X.toBlocks₂₁ 0)
        (fromBlocks X.toBlocks₂₂ M.toCols₂ᵀ M.toCols₂ 0) := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, toCols₂, hM]
  rw [← det_submatrix_equiv_self (Equiv.sumAssoc ι κ κ).symm, hre]
  exact abs_det_threeBlock _ _ _ _ _ hN
end Blocks
section Spaces
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
theorem exists_orthonormalBasis_sum_orthogonal {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (K : Submodule ℝ E) (bK : OrthonormalBasis ι ℝ K) (bP : OrthonormalBasis κ ℝ Kᗮ) :
    ∃ v : OrthonormalBasis (ι ⊕ κ) ℝ E,
      (∀ i, v (Sum.inl i) = bK i) ∧ ∀ j, v (Sum.inr j) = bP j := by
  set u : ι ⊕ κ → E := Sum.elim (fun i => (bK i : E)) (fun j => (bP j : E)) with hu
  have hon : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    have h1 := orthonormal_iff_ite.1 bK.orthonormal
    have h2 := orthonormal_iff_ite.1 bP.orthonormal
    rintro (i | i) (j | j)
    · simpa [hu, Submodule.coe_inner] using h1 i j
    · simpa [hu] using Submodule.inner_right_of_mem_orthogonal (bK i).2 (bP j).2
    · simpa [hu] using Submodule.inner_left_of_mem_orthogonal (bK j).2 (bP i).2
    · simpa [hu, Submodule.coe_inner] using h2 i j
  have hcard : Fintype.card (ι ⊕ κ) = finrank ℝ E := by
    rw [Fintype.card_sum, ← K.finrank_add_finrank_orthogonal, finrank_eq_card_basis bK.toBasis,
      finrank_eq_card_basis bP.toBasis]
  have hspan := hon.linearIndependent.span_eq_top_of_card_eq_finrank' hcard
  refine ⟨OrthonormalBasis.mk hon hspan.ge, fun i => ?_, fun j => ?_⟩
  · rw [OrthonormalBasis.coe_mk]
    rfl
  · rw [OrthonormalBasis.coe_mk]
    rfl
theorem det_saddlePointOperator_eq_det_fromBlocks {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (v : OrthonormalBasis α ℝ E) (w : OrthonormalBasis β ℝ F) (X : E →ₗ[ℝ] E) (M : E →ₗ[ℝ] F) :
    LinearMap.det (saddlePointOperator X M) =
      (fromBlocks (LinearMap.toMatrix v.toBasis v.toBasis X)
        (LinearMap.toMatrix v.toBasis w.toBasis M)ᵀ
        (LinearMap.toMatrix v.toBasis w.toBasis M) 0).det := by
  rw [← LinearMap.det_toMatrix (v.toBasis.prod w.toBasis)]
  congr 1
  have hadj : (LinearMap.toMatrix v.toBasis w.toBasis M)ᵀ =
      LinearMap.toMatrix w.toBasis v.toBasis (LinearMap.adjoint M) := by
    rw [LinearMap.toMatrix_adjoint, conjTranspose_eq_transpose_of_trivial]
  rw [hadj]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [LinearMap.toMatrix_apply, saddlePointOperator, Basis.prod_repr_inl,
      Basis.prod_repr_inr, Basis.prod_apply]
omit [FiniteDimensional ℝ E] in
theorem associated_eq_inner_apply (K : Submodule ℝ E) (T : QuadraticForm ℝ K) (X : E →ₗ[ℝ] E)
    (hX : X.IsSymmetric) (hT : ∀ B : K, inner ℝ (B : E) (X B) = T B) (x y : K) :
    QuadraticMap.associated T x y = inner ℝ (x : E) (X y) := by
  have hs : inner ℝ (y : E) (X x) = inner ℝ (x : E) (X y) := by
    rw [← hX, real_inner_comm]
  rw [QuadraticMap.associated_apply, ← hT, ← hT, ← hT]
  simp only [Submodule.coe_add, map_add, inner_add_left, inner_add_right, hs]
  simp
  ring
theorem det_pos_of_forall_inner_pos {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (Z : V →ₗ[ℝ] V) (hZ : Z.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < inner ℝ x (Z x)) : 0 < LinearMap.det Z := by
  rw [hZ.det_eq_prod_eigenvalues rfl]
  refine Finset.prod_pos fun i _ => ?_
  have hne : hZ.eigenvectorBasis rfl i ≠ 0 := (hZ.eigenvectorBasis rfl).orthonormal.ne_zero i
  have h1 := hpos _ hne
  have hn : ‖hZ.eigenvectorBasis rfl i‖ = 1 := (hZ.eigenvectorBasis rfl).orthonormal.1 i
  rw [hZ.apply_eigenvectorBasis rfl i, inner_smul_right, real_inner_self_eq_norm_sq, hn] at h1
  simpa using h1
theorem abs_det_saddlePointOperator (M : E →ₗ[ℝ] F) (hM : Function.Surjective M)
    (T : QuadraticForm ℝ (LinearMap.ker M))
    (hdet : 0 < LinearMap.det (M ∘ₗ LinearMap.adjoint M)) (X : E →ₗ[ℝ] E) (hX : X.IsSymmetric)
    (hXT : ∀ B : LinearMap.ker M, inner ℝ (B : E) (X B) = T B) (d : ℝ) (hd : 0 < d)
    (hdb : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ (LinearMap.ker M)),
      (Gaussian.KernelIntegral.formMatrixInBasis M T b).det = d) :
    |LinearMap.det (saddlePointOperator X M)| = d * LinearMap.det (M ∘ₗ LinearMap.adjoint M) := by
  have hrank : finrank ℝ (LinearMap.ker M) + finrank ℝ F = finrank ℝ E := by
    have := LinearMap.finrank_range_add_finrank_ker M
    rw [LinearMap.range_eq_top.2 hM, finrank_top] at this
    omega
  have hperp : finrank ℝ (LinearMap.ker M)ᗮ = finrank ℝ F := by
    have := (LinearMap.ker M).finrank_add_finrank_orthogonal
    omega
  let bK := stdOrthonormalBasis ℝ (LinearMap.ker M)
  let bP := (stdOrthonormalBasis ℝ (LinearMap.ker M)ᗮ).reindex (finCongr hperp)
  let w := stdOrthonormalBasis ℝ F
  obtain ⟨v, hvK, hvP⟩ := exists_orthonormalBasis_sum_orthogonal _ bK bP
  set Xm := LinearMap.toMatrix v.toBasis v.toBasis X with hXm
  set Mm := LinearMap.toMatrix v.toBasis w.toBasis M with hMmdef
  have hz : ∀ f i, Mm f (Sum.inl i) = 0 := by
    intro f i
    have hk : M (bK i : E) = 0 := (bK i).2
    simp [hMmdef, LinearMap.toMatrix_apply, hvK, hk]
  have hsplit : Mm = fromCols 0 Mm.toCols₂ := by
    ext f i
    rcases i with i | i
    · simp [hz]
    · simp [toCols₂]
  have hMM : Mm * Mmᵀ = Mm.toCols₂ * Mm.toCols₂ᵀ := by
    conv_lhs => rw [hsplit]
    rw [transpose_fromCols, fromCols_mul_fromRows]
    simp
  have hdetMM : LinearMap.det (M ∘ₗ LinearMap.adjoint M) = Mm.toCols₂.det ^ 2 := by
    have hadj : LinearMap.toMatrix w.toBasis v.toBasis (LinearMap.adjoint M) = Mmᵀ := by
      rw [LinearMap.toMatrix_adjoint, conjTranspose_eq_transpose_of_trivial]
    rw [← LinearMap.det_toMatrix w.toBasis,
      LinearMap.toMatrix_comp w.toBasis v.toBasis w.toBasis, hadj, hMM, det_mul, det_transpose, sq]
  have hA : Xm.toBlocks₁₁ = Gaussian.KernelIntegral.formMatrixInBasis M T bK := by
    ext i j
    simp [toBlocks₁₁, hXm, LinearMap.toMatrix_apply, hvK, OrthonormalBasis.repr_apply_apply,
      Gaussian.KernelIntegral.formMatrixInBasis, LinearMap.BilinForm.toMatrix_apply,
      associated_eq_inner_apply _ T X hX hXT]
  have hN : IsUnit Mm.toCols₂.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [hdetMM, h0] at hdet
    simp at hdet
  rw [det_saddlePointOperator_eq_det_fromBlocks v w, abs_det_saddleMatrix Xm Mm hz hN, hA, hdb,
    abs_of_pos hd, hdetMM]
theorem abs_det_saddlePointOperator_of_posDef (M : E →ₗ[ℝ] F) (hM : Function.Surjective M)
    (X : E →ₗ[ℝ] E) (hX : X.IsSymmetric) (hpos : ∀ B : E, B ≠ 0 → 0 < inner ℝ B (X B)) :
    |LinearMap.det (saddlePointOperator X M)| =
      LinearMap.det X *
        LinearMap.det (M ∘ₗ (Ring.inverse X : E →ₗ[ℝ] E) ∘ₗ LinearMap.adjoint M) := by
  have hinj : LinearMap.ker X = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    by_contra hne
    have := hpos m hne
    simp [hm] at this
  have hu : IsUnit X := (LinearMap.isUnit_iff_ker_eq_bot X).2 hinj
  set Y : E →ₗ[ℝ] E := Ring.inverse X with hY
  have hXY : X * Y = 1 := Ring.mul_inverse_cancel X hu
  have hXYa : ∀ e, X (Y e) = e := fun e => by
    have := congrArg (fun f : E →ₗ[ℝ] E => f e) hXY
    simpa using this
  have hYs : Y.IsSymmetric := by
    intro a b
    calc inner ℝ (Y a) b = inner ℝ (Y a) (X (Y b)) := by rw [hXYa]
      _ = inner ℝ (X (Y a)) (Y b) := (hX _ _).symm
      _ = inner ℝ a (Y b) := by rw [hXYa]
  have hadjinj : ∀ y : F, LinearMap.adjoint M y = 0 → y = 0 := by
    intro y hy
    obtain ⟨e, rfl⟩ := hM y
    have h0 : inner ℝ (LinearMap.adjoint M (M e)) e = inner ℝ (M e) (M e) :=
      LinearMap.adjoint_inner_left M e (M e)
    rw [hy, inner_zero_left] at h0
    exact inner_self_eq_zero.1 h0.symm
  set Z : F →ₗ[ℝ] F := M ∘ₗ Y ∘ₗ LinearMap.adjoint M with hZ
  have hZa : ∀ a b : F, inner ℝ a (Z b) =
      inner ℝ (LinearMap.adjoint M a) (Y (LinearMap.adjoint M b)) := by
    intro a b
    simp only [hZ, LinearMap.comp_apply]
    exact (LinearMap.adjoint_inner_left M _ a).symm
  have hZs : Z.IsSymmetric := by
    intro a b
    rw [real_inner_comm, hZa, hZa, ← hYs, real_inner_comm]
  have hZp : ∀ y : F, y ≠ 0 → 0 < inner ℝ y (Z y) := by
    intro y hy
    rw [hZa]
    have hw : Y (LinearMap.adjoint M y) ≠ 0 := by
      intro h0
      have := hXYa (LinearMap.adjoint M y)
      rw [h0, map_zero] at this
      exact hy (hadjinj y this.symm)
    have := hpos _ hw
    rw [hXYa, real_inner_comm] at this
    exact this
  have hdX : 0 < LinearMap.det X := det_pos_of_forall_inner_pos X hX hpos
  have hdZ : 0 < LinearMap.det Z := det_pos_of_forall_inner_pos Z hZs hZp
  let v := stdOrthonormalBasis ℝ E
  let w := stdOrthonormalBasis ℝ F
  set Xm := LinearMap.toMatrix v.toBasis v.toBasis X with hXm
  set Ym := LinearMap.toMatrix v.toBasis v.toBasis Y with hYm
  set Mm := LinearMap.toMatrix v.toBasis w.toBasis M with hMmdef
  have hXYm : Xm * Ym = 1 := by
    rw [hXm, hYm, ← LinearMap.toMatrix_mul, hXY, LinearMap.toMatrix_one]
  have hZm : LinearMap.toMatrix w.toBasis w.toBasis Z = Mm * Ym * Mmᵀ := by
    have hadj : LinearMap.toMatrix w.toBasis v.toBasis (LinearMap.adjoint M) = Mmᵀ := by
      rw [LinearMap.toMatrix_adjoint, conjTranspose_eq_transpose_of_trivial]
    rw [hZ, LinearMap.toMatrix_comp w.toBasis v.toBasis w.toBasis,
      LinearMap.toMatrix_comp w.toBasis v.toBasis v.toBasis, hadj, Matrix.mul_assoc]
  have hf : fromBlocks Xm Mmᵀ Mm 0 * fromBlocks 1 (-(Ym * Mmᵀ)) 0 1 =
      fromBlocks Xm 0 Mm (-(Mm * Ym * Mmᵀ)) := by
    rw [fromBlocks_multiply]
    simp [← Matrix.mul_assoc, hXYm]
  have hdf := congrArg det hf
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at hdf
  simp only [det_one, mul_one] at hdf
  rw [det_saddlePointOperator_eq_det_fromBlocks v w, hdf, det_neg, ← hZm, LinearMap.det_toMatrix,
    LinearMap.det_toMatrix, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hdX, abs_of_pos hdZ]
end Spaces
theorem saddleDeterminantFormula_of_gaussianIntegralOnKernel
    (h : Gaussian.KernelIntegral.GaussianIntegralOnKernel) : SaddleDeterminantIdentity := by
  intro E F _ _ _ _ _ _ M T hM hT X hX hXT
  obtain ⟨hdet, d, hd, hdb, -, -, hval⟩ := h E F M hM T hT
  have hkey := abs_det_saddlePointOperator M hM T hdet X hX hXT d hd hdb
  have hI : kernelGaussianIntegral M T = (2 * Real.pi) ^
      ((finrank ℝ (LinearMap.ker M) : ℝ) / 2) * d ^ (-(1 / 2) : ℝ) := hval
  have hrank : (finrank ℝ (LinearMap.ker M) : ℝ) = (finrank ℝ E : ℝ) - (finrank ℝ F : ℝ) := by
    have := LinearMap.finrank_range_add_finrank_ker M
    rw [LinearMap.range_eq_top.2 hM, finrank_top] at this
    rw [← this]
    push_cast
    ring
  refine ⟨?_, abs_det_saddlePointOperator_of_posDef M hM X hX⟩
  rw [constrainedGaussianNumber, hI, hkey, Real.mul_rpow hd.le hdet.le, hrank]
  ring
end YangMills.Construction.GaussianConstraint.SaddleDeterminant
end
