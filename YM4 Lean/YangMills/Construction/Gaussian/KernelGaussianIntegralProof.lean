import YangMills.Construction.Gaussian.KernelGaussianIntegral
import YangMills.Construction.Gaussian.PositiveDefiniteMatrixIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory Matrix
namespace YangMills.Construction.Gaussian.KernelIntegral
theorem det_comp_adjoint_pos_of_surjective {E F : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F)
    (hL : Function.Surjective L) :
    0 < LinearMap.det (L ∘ₗ LinearMap.adjoint L) := by
  have hsymm : (L ∘ₗ LinearMap.adjoint L).IsSymmetric := by
    intro x y
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right L (LinearMap.adjoint L x) y,
      ← LinearMap.adjoint_inner_left L (LinearMap.adjoint L y) x]
  rw [hsymm.det_eq_prod_eigenvalues rfl]
  refine Finset.prod_pos fun i => ?_
  have hunit : ‖hsymm.eigenvectorBasis rfl i‖ = 1 := (hsymm.eigenvectorBasis rfl).orthonormal.1 i
  have happ := hsymm.apply_eigenvectorBasis rfl i
  set v := hsymm.eigenvectorBasis rfl i with hv
  set μ : ℝ := hsymm.eigenvalues rfl i with hμ
  have hμeq : μ = ‖LinearMap.adjoint L v‖ ^ 2 := by
    have hinner : inner ℝ v ((L ∘ₗ LinearMap.adjoint L) v) = μ := by
      rw [happ]
      simp [inner_smul_right, hunit]
    rw [← hinner, LinearMap.comp_apply, ← LinearMap.adjoint_inner_left L,
      real_inner_self_eq_norm_sq]
  rw [hμeq]
  have hne : LinearMap.adjoint L v ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ := hL v
    have hadj : inner ℝ (LinearMap.adjoint L v) x = inner ℝ v (L x) :=
      LinearMap.adjoint_inner_left L x v
    rw [hzero, hx, inner_zero_left, real_inner_self_eq_norm_sq, hunit] at hadj
    norm_num at hadj
  have hsq : 0 < ‖LinearMap.adjoint L v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  first
    | exact hsq
    | simpa using hsq
section QuadraticFormMatrix
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
omit [FiniteDimensional ℝ V] in
theorem repr_dotProduct_toMatrix_mulVec (Q : QuadraticForm ℝ V) {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : OrthonormalBasis ι ℝ V) (x : V) :
    (b.repr x).ofLp ⬝ᵥ
      (LinearMap.BilinForm.toMatrix b.toBasis (QuadraticMap.associated Q)) *ᵥ (b.repr x).ofLp =
      Q x := by
  have happly := LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b.toBasis
    (QuadraticMap.associated Q) x x
  have hcoord : ⇑(b.toBasis.repr x) = (b.repr x).ofLp := by
    ext i
    simp
  rw [hcoord] at happly
  rw [← happly]
  exact QuadraticMap.associated_eq_self_apply ℝ Q x
omit [FiniteDimensional ℝ V] in
theorem toMatrix_associated_posDef (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ V) :
    (LinearMap.BilinForm.toMatrix b.toBasis (QuadraticMap.associated Q)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun y hy => ?_
  · ext i j
    simp only [conjTranspose_apply, star_trivial, LinearMap.BilinForm.toMatrix_apply]
    exact QuadraticMap.associated_isSymm ℝ Q _ _
  · have hround : b.repr (b.repr.symm (WithLp.toLp 2 y)) = WithLp.toLp 2 y := by simp
    have hval := repr_dotProduct_toMatrix_mulVec Q b (b.repr.symm (WithLp.toLp 2 y))
    rw [hround] at hval
    simp only [star_trivial]
    rw [show y ⬝ᵥ _ = _ from hval]
    apply hQ
    intro hzero
    apply hy
    have : WithLp.toLp 2 y = 0 := by
      have := congrArg b.repr hzero
      simpa using this
    simpa using congrArg WithLp.ofLp this
omit [FiniteDimensional ℝ V] in
theorem det_toMatrix_associated_eq_of_index (Q : QuadraticForm ℝ V) {ι : Type} [Fintype ι]
    [DecidableEq ι] (b c : OrthonormalBasis ι ℝ V) :
    (LinearMap.BilinForm.toMatrix c.toBasis (QuadraticMap.associated Q)).det =
      (LinearMap.BilinForm.toMatrix b.toBasis (QuadraticMap.associated Q)).det := by
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix c.toBasis b.toBasis, det_mul, det_mul,
    det_transpose]
  have hpm : (c.toBasis.toMatrix b).det = 1 ∨ (c.toBasis.toMatrix b).det = -1 := by
    simpa [Module.Basis.det_apply] using c.det_to_matrix_orthonormalBasis_real b
  rcases hpm with hpm | hpm <;> simp [hpm]
theorem det_toMatrix_associated_eq (Q : QuadraticForm ℝ V) {ι κ : Type} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : OrthonormalBasis ι ℝ V)
    (c : OrthonormalBasis κ ℝ V) :
    (LinearMap.BilinForm.toMatrix c.toBasis (QuadraticMap.associated Q)).det =
      (LinearMap.BilinForm.toMatrix b.toBasis (QuadraticMap.associated Q)).det := by
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis c.toBasis, ← Module.finrank_eq_card_basis b.toBasis]
  let σ : κ ≃ ι := Fintype.equivOfCardEq hcard
  have hre : LinearMap.BilinForm.toMatrix (c.reindex σ).toBasis (QuadraticMap.associated Q) =
      (LinearMap.BilinForm.toMatrix c.toBasis (QuadraticMap.associated Q)).submatrix σ.symm
        σ.symm := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  rw [← det_toMatrix_associated_eq_of_index Q b (c.reindex σ), hre, det_submatrix_equiv_self]
theorem integral_exp_neg_half_eq [MeasurableSpace V] [BorelSpace V]
    (hG : YangMills.Construction.Gaussian.PosDefMatrix.RealGaussianIntegral)
    (Q : QuadraticForm ℝ V) (hQ : Q.PosDef)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V) :
    ∫ x : V, Real.exp (-(1 / 2) * Q x) =
      (2 * Real.pi) ^ ((Module.finrank ℝ V : ℝ) / 2) /
        Real.sqrt (LinearMap.BilinForm.toMatrix b.toBasis (QuadraticMap.associated Q)).det := by
  set A := LinearMap.BilinForm.toMatrix b.toBasis (QuadraticMap.associated Q) with hA
  rw [← hG _ A (toMatrix_associated_posDef Q hQ b)]
  have hcoords : ∫ x : V, Real.exp (-(1 / 2) * Q x) =
      ∫ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
        Real.exp (-(1 / 2) * (y.ofLp ⬝ᵥ A *ᵥ y.ofLp)) := by
    rw [← b.measurePreserving_measurableEquiv.integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hmeq : b.measurableEquiv x = b.repr x := rfl
    show _ = Real.exp (-(1 / 2) * ((b.measurableEquiv x).ofLp ⬝ᵥ A *ᵥ (b.measurableEquiv x).ofLp))
    rw [hmeq, hA, repr_dotProduct_toMatrix_mulVec]
  rw [hcoords]
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).integral_comp'
    (fun z : Fin (Module.finrank ℝ V) → ℝ => Real.exp (-(1 / 2) * (z ⬝ᵥ A *ᵥ z)))
end QuadraticFormMatrix
theorem gaussianIntegralOnKernel_holds
    (hG : YangMills.Construction.Gaussian.PosDefMatrix.RealGaussianIntegral) :
    GaussianIntegralOnKernel := by
  intro E F _ _ _ _ _ _ L hL Q hQ
  refine ⟨det_comp_adjoint_pos_of_surjective L hL, ?_⟩
  let b₀ := stdOrthonormalBasis ℝ (LinearMap.ker L)
  have hpd := toMatrix_associated_posDef Q hQ b₀
  refine ⟨(LinearMap.BilinForm.toMatrix b₀.toBasis (QuadraticMap.associated Q)).det,
    hpd.det_pos, ?_, ?_⟩
  · intro ι _ _ b
    exact det_toMatrix_associated_eq Q b₀ b
  · letI : MeasurableSpace (LinearMap.ker L) := borel _
    haveI : BorelSpace (LinearMap.ker L) := ⟨rfl⟩
    have hd := hpd.det_pos
    set d := (LinearMap.BilinForm.toMatrix b₀.toBasis (QuadraticMap.associated Q)).det with hd_def
    have hint := integral_exp_neg_half_eq hG Q hQ b₀
    rw [← hd_def] at hint
    have hform : (2 * Real.pi) ^ ((Module.finrank ℝ (LinearMap.ker L) : ℝ) / 2) / Real.sqrt d =
        (2 * Real.pi) ^ ((Module.finrank ℝ (LinearMap.ker L) : ℝ) / 2) * d ^ (-(1 / 2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hd.le, div_eq_mul_inv]
    have hpos : 0 < ∫ x : LinearMap.ker L, Real.exp (-(1 / 2) * Q x) := by
      rw [hint, hform]
      have := Real.pi_pos
      positivity
    refine ⟨?_, hpos, hint.trans hform⟩
    by_contra hnot
    rw [integral_undef hnot] at hpos
    exact lt_irrefl _ hpos
end YangMills.Construction.Gaussian.KernelIntegral
