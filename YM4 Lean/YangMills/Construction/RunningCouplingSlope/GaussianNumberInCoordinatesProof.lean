import YangMills.Construction.RunningCouplingSlope.ChangeOfGaugeInAGaussianNumberProof
import YangMills.Construction.RunningCouplingSlope.GaussianNumberInCoordinates
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Module MeasureTheory
noncomputable section
namespace YangMills.Construction.LinearConstraint.GaussianFormula
section Determinants
variable {V W U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
private theorem det_id_add_comp_swap (A : W →ₗ[ℝ] V) (B : V →ₗ[ℝ] W) :
    LinearMap.det (LinearMap.id + A ∘ₗ B) = LinearMap.det (LinearMap.id + B ∘ₗ A) := by apply _root_.YangMills.Construction.LinearConstraint.GaugeChangeProof.det_id_add_comp_comm <;> assumption
private theorem nonempty_linearIsometryEquiv_of_finrank (h : finrank ℝ V = finrank ℝ W) : Nonempty (V ≃ₗᵢ[ℝ] W) := by apply _root_.YangMills.Construction.LinearConstraint.GaugeChangeProof.nonempty_linearIsometryEquiv_of_finrank_eq <;> assumption
private theorem absDetOfMap_eq_abs_det (e : W ≃ₗᵢ[ℝ] V) (A : V →ₗ[ℝ] W) :
    absDetOfMap A = |LinearMap.det (e.toLinearEquiv.toLinearMap ∘ₗ A)| := by apply _root_.YangMills.Construction.LinearConstraint.GaugeChangeProof.absDetOfMap_eq_abs_det_comp <;> assumption
private theorem absDetOfMap_comp (A : V →ₗ[ℝ] W) (B : U →ₗ[ℝ] V) (h₁ : finrank ℝ U = finrank ℝ V)
    (h₂ : finrank ℝ V = finrank ℝ W) :
    absDetOfMap (A ∘ₗ B) = absDetOfMap A * absDetOfMap B := by apply _root_.YangMills.Construction.LinearConstraint.GaugeChangeProof.absDetOfMap_comp <;> assumption
private theorem det_ne_zero_of_bijective' (f : V →ₗ[ℝ] V) (h : Function.Bijective f) :
    LinearMap.det f ≠ 0 :=
  ((LinearEquiv.ofBijective f h).isUnit_det').ne_zero
private theorem integral_comp_linearMap [MeasurableSpace V] [BorelSpace V] (φ : V →ₗ[ℝ] V)
    (hφ : LinearMap.det φ ≠ 0) (f : V → ℝ) :
    ∫ x, f (φ x) = |(LinearMap.det φ)⁻¹| * ∫ x, f x := by apply _root_.YangMills.Construction.LinearConstraint.GaugeChangeProof.integral_comp_linearMap_of_det_ne_zero <;> assumption
private theorem integral_eq_absDetOfMap_mul [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    (A : V →ₗ[ℝ] W) (hA : Function.Bijective A) (f : W → ℝ) :
    ∫ y, f y = absDetOfMap A * ∫ x, f (A x) := by
  have hr : finrank ℝ W = finrank ℝ V := (LinearEquiv.ofBijective A hA).finrank_eq.symm
  obtain ⟨e⟩ := nonempty_linearIsometryEquiv_of_finrank hr
  let φ : V →ₗ[ℝ] V := e.toLinearEquiv.toLinearMap ∘ₗ A
  have hφb : Function.Bijective φ := e.toLinearEquiv.bijective.comp hA
  have hφ : LinearMap.det φ ≠ 0 := det_ne_zero_of_bijective' φ hφb
  have hv : absDetOfMap A = |LinearMap.det φ| := absDetOfMap_eq_abs_det e A
  have h1 : ∫ y, f y = ∫ x, f (e.symm x) :=
    ((e.symm.measurePreserving).integral_comp' (f := e.symm.toHomeomorph.toMeasurableEquiv) f).symm
  have h2 := integral_comp_linearMap φ hφ (fun x => f (e.symm x))
  have h3 : ∀ x, e.symm (φ x) = A x := fun x => by simp [φ]
  simp only [h3] at h2
  rw [h1, h2, hv, abs_inv]
  have : |LinearMap.det φ| ≠ 0 := abs_ne_zero.mpr hφ
  field_simp
end Determinants
section Gauss
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
private def matrixEuclideanMap (B : Matrix Ω Ω ℝ) : EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℝ Ω :=
  (WithLp.linearEquiv 2 ℝ (Ω → ℝ)).symm.toLinearMap ∘ₗ Matrix.toLin' B ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Ω → ℝ)).toLinearMap
private theorem det_matrixEuclideanMap (B : Matrix Ω Ω ℝ) : LinearMap.det (matrixEuclideanMap B) = B.det := by
  have := LinearMap.det_conj (Matrix.toLin' B) (WithLp.linearEquiv 2 ℝ (Ω → ℝ)).symm
  rw [LinearMap.det_toLin'] at this
  simpa [matrixEuclideanMap, LinearMap.comp_assoc] using this
private theorem norm_sq_matrixEuclideanMap (B : Matrix Ω Ω ℝ) (u : EuclideanSpace ℝ Ω) :
    ‖matrixEuclideanMap B u‖ ^ 2 = dotProduct (WithLp.ofLp u) (Matrix.mulVec (B.transpose * B) (WithLp.ofLp u)) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hcoord : ∀ i, (matrixEuclideanMap B u) i = Matrix.mulVec B (WithLp.ofLp u) i := fun i => by
    simp [matrixEuclideanMap, Matrix.toLin'_apply]
  simp only [hcoord]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp [dotProduct, sq]
private theorem PosDef.exists_eq_transpose_mul_self (G : Matrix Ω Ω ℝ) (hG : G.PosDef) :
    ∃ B : Matrix Ω Ω ℝ, G = B.transpose * B := by
  have hH := hG.isHermitian
  let A : Matrix Ω Ω ℝ := (hH.eigenvectorUnitary : Matrix Ω Ω ℝ)
  let r : Ω → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  refine ⟨Matrix.diagonal r * A.transpose, ?_⟩
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hd : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) = Matrix.diagonal r * Matrix.diagonal r := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [r, Real.mul_self_sqrt (hG.eigenvalues_pos i).le]
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
  calc G = A * (Matrix.diagonal r * Matrix.diagonal r) * star A := by rw [← hd]; exact hs
    _ = A * Matrix.diagonal r * (Matrix.diagonal r * A.transpose) := by
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        simp only [A, Matrix.mul_assoc]
theorem integral_exp_neg_half_quadForm (G : Matrix Ω Ω ℝ) (hG : G.PosDef) :
    ∫ u : EuclideanSpace ℝ Ω, Real.exp (-(1 / 2) * dotProduct (WithLp.ofLp u) (Matrix.mulVec G (WithLp.ofLp u))) =
      (2 * Real.pi) ^ ((Fintype.card Ω : ℝ) / 2) * G.det ^ (-(1 / 2) : ℝ) := by
  obtain ⟨B, rfl⟩ := PosDef.exists_eq_transpose_mul_self G hG
  have hdet : (B.transpose * B).det = B.det ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose, sq]
  have hpos : 0 < (B.transpose * B).det := hG.det_pos
  have hB : B.det ≠ 0 := by
    intro h
    rw [hdet, h] at hpos
    simp at hpos
  have h1 := integral_comp_linearMap (matrixEuclideanMap B) (by rw [det_matrixEuclideanMap]; exact hB)
    (fun v => Real.exp (-(1 / 2) * ‖v‖ ^ 2))
  simp only [norm_sq_matrixEuclideanMap] at h1
  rw [h1, GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num), det_matrixEuclideanMap, hdet]
  have h2 : Real.pi / (1 / 2) = 2 * Real.pi := by ring
  have h3 : (B.det ^ 2) ^ (-(1 / 2) : ℝ) = |B.det|⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  rw [h2, h3, finrank_euclideanSpace, abs_inv, mul_comm]
end Gauss
theorem gaussianNumberCoordinateFormula_aux : GaussianNumberCoordinateFormula := by
  intro E E₁ C _ _ _ _ _ _ _ _ _ Ω _ _ p q s j M T Ψ G horth hps hqs hpj hqj hMj hG hb hT
  have hps' : ∀ e, p (s e) = e := fun e => LinearMap.congr_fun hps e
  have hqs' : ∀ e, q (s e) = 0 := fun e => LinearMap.congr_fun hqs e
  have hpj' : ∀ c, p (j c) = 0 := fun c => LinearMap.congr_fun hpj c
  have hqj' : ∀ c, q (j c) = c := fun c => LinearMap.congr_fun hqj c
  have hMj' : ∀ c, M (j c) = c := fun c => LinearMap.congr_fun hMj c
  have hdec : ∀ ξ, ξ = s (p ξ) + j (q ξ) := by
    intro ξ
    have h0 : inner ℝ (ξ - (s (p ξ) + j (q ξ))) (ξ - (s (p ξ) + j (q ξ))) = (0 : ℝ) := by
      rw [horth]
      simp [hps', hqs', hpj', hqj']
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)
  let Bm : E₁ →ₗ[ℝ] C := M ∘ₗ s
  have hM : ∀ ξ, M ξ = Bm (p ξ) + q ξ := by
    intro ξ
    conv_lhs => rw [hdec ξ]
    simp [Bm, hMj']
  have hadjp : LinearMap.adjoint p = s := by
    refine LinearMap.ext fun e => ext_inner_right ℝ fun ξ => ?_
    rw [LinearMap.adjoint_inner_left, real_inner_comm (p ξ), real_inner_comm ξ, horth]
    simp [hps', hqs']
  have hadjq : LinearMap.adjoint q = j := by
    refine LinearMap.ext fun e => ext_inner_right ℝ fun ξ => ?_
    rw [LinearMap.adjoint_inner_left, real_inner_comm (q ξ), real_inner_comm ξ, horth]
    simp [hpj', hqj']
  have hMform : M = Bm ∘ₗ p + q := LinearMap.ext fun ξ => by simp [hM]
  have hadjM : LinearMap.adjoint M = s ∘ₗ LinearMap.adjoint Bm + j := by
    rw [hMform, map_add, LinearMap.adjoint_comp, hadjp, hadjq]
  have hMM : M ∘ₗ LinearMap.adjoint M = LinearMap.id + Bm ∘ₗ LinearMap.adjoint Bm := by
    rw [hadjM]
    refine LinearMap.ext fun c => ?_
    simp [hM, hps', hqs', hpj', hqj', add_comm]
  let h₀ : E₁ →ₗ[ℝ] E := s - j ∘ₗ Bm
  have hh₀ : ∀ e, h₀ e ∈ LinearMap.ker M := fun e => by
    refine LinearMap.mem_ker.mpr ?_
    show M (s e - j (Bm e)) = 0
    rw [map_sub, hMj']
    exact sub_eq_zero.mpr rfl
  let h : E₁ →ₗ[ℝ] LinearMap.ker M := h₀.codRestrict _ hh₀
  have hhval : ∀ e, ((h e : LinearMap.ker M) : E) = s e - j (Bm e) := fun e => rfl
  have hhh : LinearMap.adjoint h ∘ₗ h = LinearMap.id + LinearMap.adjoint Bm ∘ₗ Bm := by
    refine LinearMap.ext fun e => ext_inner_right ℝ fun e' => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    simp only [Submodule.coe_inner, hhval, horth]
    simp [hps', hqs', hpj', hqj', inner_add_left, LinearMap.adjoint_inner_left]
  have hret : ∀ ξ : LinearMap.ker M, h (p (ξ : E)) = ξ := by
    intro ξ
    apply Subtype.ext
    rw [hhval]
    have hz : Bm (p (ξ : E)) = -q (ξ : E) := by
      have := hM (ξ : E)
      rw [LinearMap.mem_ker.mp ξ.2] at this
      exact eq_neg_of_add_eq_zero_left this.symm
    rw [hz, map_neg, sub_neg_eq_add]
    exact (hdec _).symm
  set ψ : EuclideanSpace ℝ Ω →ₗ[ℝ] E₁ := p ∘ₗ (LinearMap.ker M).subtype ∘ₗ Ψ with hψ
  have hΨ : Ψ = h ∘ₗ ψ := LinearMap.ext fun u => (hret (Ψ u)).symm
  have hhb : Function.Bijective h := by
    constructor
    · intro e e' hee
      have := congrArg (fun ξ : LinearMap.ker M => p (ξ : E)) hee
      simpa [hhval, hps', hpj'] using this
    · intro ξ
      exact ⟨p (ξ : E), hret ξ⟩
  have hΨb : Function.Bijective Ψ := by
    rw [hΨ]
    exact hhb.comp hb
  have r₁ : finrank ℝ (EuclideanSpace ℝ Ω) = finrank ℝ E₁ := (LinearEquiv.ofBijective ψ hb).finrank_eq
  have r₂ : finrank ℝ E₁ = finrank ℝ (LinearMap.ker M) := (LinearEquiv.ofBijective h hhb).finrank_eq
  have hvol : absDetOfMap Ψ = absDetOfMap h * absDetOfMap ψ := by
    rw [hΨ]; exact absDetOfMap_comp h ψ r₁ r₂
  have hvh : absDetOfMap h = Real.sqrt (LinearMap.det (M ∘ₗ LinearMap.adjoint M)) := by
    rw [absDetOfMap, hhh, hMM, det_id_add_comp_swap]
  have hvh0 : absDetOfMap h ≠ 0 := by
    obtain ⟨e⟩ := nonempty_linearIsometryEquiv_of_finrank r₂.symm
    rw [absDetOfMap_eq_abs_det e h]
    exact abs_ne_zero.mpr (det_ne_zero_of_bijective' _ (e.toLinearEquiv.bijective.comp hhb))
  have hdp : 0 < LinearMap.det (M ∘ₗ LinearMap.adjoint M) := by
    have := hvh ▸ hvh0
    exact Real.sqrt_ne_zero'.mp this
  unfold GaussianConstraint.constrainedGaussianNumber GaussianConstraint.kernelGaussianIntegral
  letI : MeasurableSpace (LinearMap.ker M) := borel _
  haveI : BorelSpace (LinearMap.ker M) := ⟨rfl⟩
  rw [integral_eq_absDetOfMap_mul Ψ hΨb]
  simp only [hT]
  rw [integral_exp_neg_half_quadForm G hG, hvol, hvh, Real.sqrt_eq_rpow]
  have hone : LinearMap.det (M ∘ₗ LinearMap.adjoint M) ^ (-(1 / 2) : ℝ) *
      LinearMap.det (M ∘ₗ LinearMap.adjoint M) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hdp]; simp
  calc _ = (LinearMap.det (M ∘ₗ LinearMap.adjoint M) ^ (-(1 / 2) : ℝ) *
        LinearMap.det (M ∘ₗ LinearMap.adjoint M) ^ (1 / 2 : ℝ)) *
        (absDetOfMap ψ * ((2 * Real.pi) ^ ((Fintype.card Ω : ℝ) / 2) * G.det ^ (-(1 / 2) : ℝ))) := by ring
    _ = _ := by rw [hone]; ring
end YangMills.Construction.LinearConstraint.GaussianFormula
end
