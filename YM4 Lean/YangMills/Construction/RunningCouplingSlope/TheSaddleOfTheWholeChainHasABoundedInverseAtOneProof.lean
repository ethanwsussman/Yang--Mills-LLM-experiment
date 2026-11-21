import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheGhostOfTheWholeChainHasABoundedInverseAtOneProof
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreIsSmoothProof
import YangMills.Construction.RunningCouplingSlope.AveragesAlongTheBackgroundAreLocal
import YangMills.Construction.RunningCouplingSlope.BoundedInversesOfLocalMatricesAreLocal
import YangMills.Construction.RunningCouplingSlope.ColourCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOne
import YangMills.Construction.RunningCouplingSlope.FreeInversesOnASideAreLocal
import YangMills.Construction.RunningCouplingSlope.FreeRootsOnASideAreLocal
import YangMills.Construction.RunningCouplingSlope.MatrixOfTheBackgroundOperator
import YangMills.Construction.RunningCouplingSlope.NoiseAndCovarianceAtOneArePositive
import YangMills.Construction.RunningCouplingSlope.NoiseKernelInThePlainChain
import YangMills.Construction.RunningCouplingSlope.NoiseMatrixAtOneHasALocalInverse
import YangMills.Construction.RunningCouplingSlope.OtherConstraintAtNoNoise
import YangMills.Construction.RunningCouplingSlope.PlainIteratesNearOne
import YangMills.Construction.RunningCouplingSlope.PlainKernelsGiveTheirMaps
import YangMills.Construction.RunningCouplingSlope.PlainStepOnTheForms
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheSoftAction
import YangMills.Construction.RunningCouplingSlope.TheSaddleOfTheWholeChainHasABoundedInverseAtOne
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
open Matrix Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace SaddleInverseAtIdentity
open Tower PeriodicOperators Matrices
section Vectors
open scoped Matrix.Norms.L2Operator
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
private def vnorm (v : ι → ℂ) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖
private theorem vnorm_nonneg (v : ι → ℂ) : 0 ≤ vnorm v := norm_nonneg _
private theorem vnorm_add_le (u v : ι → ℂ) : vnorm (u + v) ≤ vnorm u + vnorm v := by
  unfold vnorm
  rw [WithLp.toLp_add]
  exact norm_add_le _ _
private theorem vnorm_neg (v : ι → ℂ) : vnorm (-v) = vnorm v := by
  unfold vnorm
  rw [WithLp.toLp_neg, norm_neg]
private theorem vnorm_sub_le (u v : ι → ℂ) : vnorm (u - v) ≤ vnorm u + vnorm v := by
  rw [sub_eq_add_neg]
  exact (vnorm_add_le _ _).trans (by rw [vnorm_neg])
private theorem vnorm_smul (c : ℂ) (v : ι → ℂ) : vnorm (c • v) = ‖c‖ * vnorm v := by
  unfold vnorm
  rw [WithLp.toLp_smul, norm_smul]
private theorem vnorm_mulVec_le [DecidableEq ι] (A : Matrix ι' ι ℂ) (v : ι → ℂ) :
    vnorm (A *ᵥ v) ≤ ‖A‖ * vnorm v :=
  Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)
private theorem vnorm_sq (v : ι → ℂ) : vnorm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  unfold vnorm
  rw [EuclideanSpace.norm_sq_eq]
private theorem vnorm_eq_zero {v : ι → ℂ} (h : vnorm v = 0) : v = 0 := by
  have h2 := norm_eq_zero.1 h
  exact (WithLp.toLp_injective 2) (by rw [h2]; rfl)
private theorem vnorm_comp_inl_le (v : ι ⊕ ι' → ℂ) : vnorm (v ∘ Sum.inl) ≤ vnorm v := by
  refine abs_le_of_sq_le_sq' ?_ (vnorm_nonneg _) |>.2
  rw [vnorm_sq, vnorm_sq, Fintype.sum_sum_type]
  have : 0 ≤ ∑ i, ‖v (Sum.inr i)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  simp only [Function.comp_apply]
  linarith
private theorem vnorm_comp_inr_le (v : ι ⊕ ι' → ℂ) : vnorm (v ∘ Sum.inr) ≤ vnorm v := by
  refine abs_le_of_sq_le_sq' ?_ (vnorm_nonneg _) |>.2
  rw [vnorm_sq, vnorm_sq, Fintype.sum_sum_type]
  have : 0 ≤ ∑ i, ‖v (Sum.inl i)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  simp only [Function.comp_apply]
  linarith
private theorem vnorm_elim_le (u : ι → ℂ) (w : ι' → ℂ) :
    vnorm (Sum.elim u w) ≤ vnorm u + vnorm w := by
  refine abs_le_of_sq_le_sq' ?_ (add_nonneg (vnorm_nonneg _) (vnorm_nonneg _)) |>.2
  rw [vnorm_sq, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have h1 := vnorm_sq u
  have h2 := vnorm_sq w
  nlinarith [vnorm_nonneg u, vnorm_nonneg w, mul_nonneg (vnorm_nonneg u) (vnorm_nonneg w)]
private theorem inv_bound_of_lower [DecidableEq ι] (S : Matrix ι ι ℂ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v, vnorm v ≤ K * vnorm (S *ᵥ v)) : IsUnit (Matrix.det S) ∧ ‖S⁻¹‖ ≤ K := by
  have hdet : IsUnit (Matrix.det S) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hSv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 := h v
    rw [hSv] at h1
    have h2 : vnorm (0 : ι → ℂ) = 0 := by
      simp [vnorm]
    rw [h2, mul_zero] at h1
    exact hv (vnorm_eq_zero (le_antisymm h1 (vnorm_nonneg _)))
  refine ⟨hdet, ?_⟩
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  have h1 := h (S⁻¹ *ᵥ x.ofLp)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hdet, Matrix.one_mulVec] at h1
  have e1 : vnorm x.ofLp = ‖x‖ := by simp [vnorm]
  have e2 : vnorm (S⁻¹ *ᵥ x.ofLp) = ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) S⁻¹ x‖ := by
    unfold vnorm
    rw [← Matrix.ofLp_toEuclideanCLM]
  rwa [e1, e2] at h1
end Vectors
section Saddle
open scoped Matrix.Norms.L2Operator
variable {I J T : Type} [Fintype I] [Fintype J] [Fintype T] [DecidableEq I] [DecidableEq J]
  [DecidableEq T]
private def saddleConstant (a η bz bq bn bm : ℝ) : ℝ :=
  (bz * (η⁻¹ ^ 2 + 2 * bq * (bn * (η * (1 + a⁻¹ * bm) + 2 * (bq * (bz * η⁻¹ ^ 2))))))
    + a⁻¹ * (1 + bm * (η⁻¹ * (bn * (η * (1 + a⁻¹ * bm) + 2 * (bq * (bz * η⁻¹ ^ 2))))))
    + η⁻¹ * (bn * (η * (1 + a⁻¹ * bm) + 2 * (bq * (bz * η⁻¹ ^ 2))))
private theorem saddle_elimination (Xi Z : Matrix I I ℂ) (hZ : Z * Xi = 1) (Q : Matrix T I ℂ)
    (Qt : Matrix I T ℂ) (G : Matrix T T ℂ) (Ni : Matrix (T ⊕ T) (T ⊕ T) ℂ)
    (hNi : Ni * Matrix.fromBlocks (-G - Q * Z * Qt) (-(Q * Z * Qt)) (-(Q * Z * Qt))
      (1 - Q * Z * Qt) = 1)
    (x ft : I → ℂ) (y gt : T → ℂ)
    (e1 : ft = Xi *ᵥ x + Qt *ᵥ (-(Q *ᵥ x)) + Qt *ᵥ y)
    (e3 : gt = Q *ᵥ x - G *ᵥ y) :
    x = Z *ᵥ (ft - Qt *ᵥ (-(Q *ᵥ x)) - Qt *ᵥ y) ∧
      Sum.elim y (-(Q *ᵥ x)) = Ni *ᵥ Sum.elim (gt - Q *ᵥ (Z *ᵥ ft)) (-(Q *ᵥ (Z *ᵥ ft))) := by
  have hx : x = Z *ᵥ (ft - Qt *ᵥ (-(Q *ᵥ x)) - Qt *ᵥ y) := by
    have e : ft - Qt *ᵥ (-(Q *ᵥ x)) - Qt *ᵥ y = Xi *ᵥ x := by
      rw [e1]
      abel
    rw [e, Matrix.mulVec_mulVec, hZ, Matrix.one_mulVec]
  refine ⟨hx, ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, w = -(Q *ᵥ x) := ⟨_, rfl⟩
  rw [← hw] at hx e1 ⊢
  have hq : Q *ᵥ x = -w := by rw [hw, neg_neg]
  have hzx : Z *ᵥ (Qt *ᵥ w) + Z *ᵥ (Qt *ᵥ y) = Z *ᵥ ft - x := by
    have hx' : Z *ᵥ ft - Z *ᵥ (Qt *ᵥ w) - Z *ᵥ (Qt *ᵥ y) = x := by
      rw [← Matrix.mulVec_sub, ← Matrix.mulVec_sub]
      exact hx.symm
    linear_combination (norm := module) (-1 : ℂ) • hx'
  have hqz : Q *ᵥ (Z *ᵥ (Qt *ᵥ w)) + Q *ᵥ (Z *ᵥ (Qt *ᵥ y)) = Q *ᵥ (Z *ᵥ ft) + w := by
    rw [← Matrix.mulVec_add, hzx, Matrix.mulVec_sub, hq]
    abel
  have hN : Matrix.fromBlocks (-G - Q * Z * Qt) (-(Q * Z * Qt)) (-(Q * Z * Qt))
      (1 - Q * Z * Qt) *ᵥ Sum.elim y w =
      Sum.elim (gt - Q *ᵥ (Z *ᵥ ft)) (-(Q *ᵥ (Z *ᵥ ft))) := by
    rw [Matrix.fromBlocks_mulVec]
    have c1 : Sum.elim y w ∘ Sum.inl = y := by
      funext i
      rfl
    have c2 : Sum.elim y w ∘ Sum.inr = w := by
      funext i
      rfl
    rw [c1, c2]
    have a1 : (Q * Z * Qt) *ᵥ y = Q *ᵥ (Z *ᵥ (Qt *ᵥ y)) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have a2 : (Q * Z * Qt) *ᵥ w = Q *ᵥ (Z *ᵥ (Qt *ᵥ w)) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    congr 1
    · rw [Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.neg_mulVec, a1, a2, e3, hq]
      linear_combination (norm := module) (-1 : ℂ) • hqz
    · rw [Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec, a1, a2]
      linear_combination (norm := module) (-1 : ℂ) • hqz
  rw [← hN, Matrix.mulVec_mulVec, hNi, Matrix.one_mulVec]
private theorem vnorm_le_saddleConstant_mul (Xi Z : Matrix I I ℂ) (hZ : Z * Xi = 1)
    (Q : Matrix T I ℂ) (Qt : Matrix I T ℂ) (G : Matrix T T ℂ) (Ni : Matrix (T ⊕ T) (T ⊕ T) ℂ)
    (hNi : Ni * Matrix.fromBlocks (-G - Q * Z * Qt) (-(Q * Z * Qt)) (-(Q * Z * Qt))
      (1 - Q * Z * Qt) = 1)
    (Mn : Matrix T J ℂ) {a η : ℝ} (ha : 0 < a) (hη : 0 < η)
    (hG : G = ((a⁻¹ : ℝ) : ℂ) • (Mn * Mn.transpose))
    (hQt : (((η⁻¹ : ℝ) : ℂ) • Q).transpose = ((η ^ 3 : ℝ) : ℂ) • Qt)
    {bz bq bn bm : ℝ} (hbz : ‖Z‖ ≤ bz) (hbq : ‖Q‖ ≤ bq) (hbq' : ‖Qt‖ ≤ bq) (hbn : ‖Ni‖ ≤ bn)
    (hbm : ‖Mn‖ ≤ bm) (hbm' : ‖Mn.transpose‖ ≤ bm)
    (v : (I ⊕ J) ⊕ T → ℂ) :
    vnorm v ≤ saddleConstant a η bz bq bn bm * vnorm (Matrix.fromBlocks
      (Matrix.fromBlocks (((η ^ 2 : ℝ) : ℂ) • (Xi - Qt * Q)) 0 0 ((a : ℂ) • 1))
      (Matrix.fromCols (((η⁻¹ : ℝ) : ℂ) • Q) Mn).transpose
      (Matrix.fromCols (((η⁻¹ : ℝ) : ℂ) • Q) Mn) 0 *ᵥ v) := by
  have hac : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hηc : ((η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hbz0 : 0 ≤ bz := (norm_nonneg _).trans hbz
  have hbq0 : 0 ≤ bq := (norm_nonneg _).trans hbq
  have hbn0 : 0 ≤ bn := (norm_nonneg _).trans hbn
  have hbm0 : 0 ≤ bm := (norm_nonneg _).trans hbm
  obtain ⟨x, hxd⟩ : ∃ x, x = fun i => v (.inl (.inl i)) := ⟨_, rfl⟩
  obtain ⟨z, hzd⟩ : ∃ z, z = fun i => v (.inl (.inr i)) := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y, y = fun i => v (.inr i) := ⟨_, rfl⟩
  have hv : v = Sum.elim (Sum.elim x z) y := by
    funext i
    rcases i with (i | i) | i <;> simp [hxd, hzd, hyd]
  obtain ⟨w, hw⟩ : ∃ w, w = Matrix.fromBlocks
      (Matrix.fromBlocks (((η ^ 2 : ℝ) : ℂ) • (Xi - Qt * Q)) 0 0 ((a : ℂ) • 1))
      (Matrix.fromCols (((η⁻¹ : ℝ) : ℂ) • Q) Mn).transpose
      (Matrix.fromCols (((η⁻¹ : ℝ) : ℂ) • Q) Mn) 0 *ᵥ v := ⟨_, rfl⟩
  rw [← hw]
  obtain ⟨f, hf⟩ : ∃ f, f = (w ∘ Sum.inl) ∘ Sum.inl := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = (w ∘ Sum.inl) ∘ Sum.inr := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = w ∘ Sum.inr := ⟨_, rfl⟩
  have nf : vnorm f ≤ vnorm w := by
    rw [hf]
    exact (vnorm_comp_inl_le _).trans (vnorm_comp_inl_le _)
  have nh : vnorm h ≤ vnorm w := by
    rw [hh]
    exact (vnorm_comp_inr_le _).trans (vnorm_comp_inl_le _)
  have ng : vnorm g ≤ vnorm w := by
    rw [hg]
    exact vnorm_comp_inr_le _
  have c1 : (Sum.elim (Sum.elim x z) y : (I ⊕ J) ⊕ T → ℂ) ∘ Sum.inl = Sum.elim x z := by
    funext i
    rfl
  have c2 : (Sum.elim (Sum.elim x z) y : (I ⊕ J) ⊕ T → ℂ) ∘ Sum.inr = y := by
    funext i
    rfl
  have c3 : (Sum.elim x z : I ⊕ J → ℂ) ∘ Sum.inl = x := by
    funext i
    rfl
  have c4 : (Sum.elim x z : I ⊕ J → ℂ) ∘ Sum.inr = z := by
    funext i
    rfl
  have hwe : w = Sum.elim (Sum.elim
      (((η ^ 2 : ℝ) : ℂ) • (Xi *ᵥ x - Qt *ᵥ (Q *ᵥ x)) + ((η ^ 3 : ℝ) : ℂ) • (Qt *ᵥ y))
      ((a : ℂ) • z + Mn.transpose *ᵥ y))
      (((η⁻¹ : ℝ) : ℂ) • (Q *ᵥ x) + Mn *ᵥ z) := by
    rw [hw, hv, Matrix.fromBlocks_mulVec, c1, c2, Matrix.fromBlocks_mulVec, c3, c4,
      Matrix.transpose_fromCols, Matrix.fromRows_mulVec, hQt, Matrix.fromCols_mulVec, c3, c4]
    simp only [Matrix.zero_mulVec, add_zero, zero_add, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    funext i
    rcases i with (i | i) | i <;> simp
  have e1 : f = ((η ^ 2 : ℝ) : ℂ) • (Xi *ᵥ x - Qt *ᵥ (Q *ᵥ x)) +
      ((η ^ 3 : ℝ) : ℂ) • (Qt *ᵥ y) := by
    rw [hf, hwe]
    rfl
  have e2 : h = (a : ℂ) • z + Mn.transpose *ᵥ y := by
    rw [hh, hwe]
    rfl
  have e3 : g = ((η⁻¹ : ℝ) : ℂ) • (Q *ᵥ x) + Mn *ᵥ z := by
    rw [hg, hwe]
    rfl
  obtain ⟨y', hy'⟩ : ∃ y', y' = ((η : ℝ) : ℂ) • y := ⟨_, rfl⟩
  obtain ⟨ft, hft⟩ : ∃ ft, ft = (((η⁻¹ ^ 2 : ℝ)) : ℂ) • f := ⟨_, rfl⟩
  obtain ⟨gt, hgt⟩ : ∃ gt, gt = ((η : ℝ) : ℂ) •
      (g - ((a⁻¹ : ℝ) : ℂ) • (Mn *ᵥ h)) := ⟨_, rfl⟩
  have hz : z = ((a⁻¹ : ℝ) : ℂ) • (h - Mn.transpose *ᵥ y) := by
    rw [e2, add_sub_cancel_right, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hac, one_smul]
  have f1 : ft = Xi *ᵥ x + Qt *ᵥ (-(Q *ᵥ x)) + Qt *ᵥ y' := by
    rw [hft, e1, hy', Matrix.mulVec_smul, Matrix.mulVec_neg]
    have n1 : (((η⁻¹ ^ 2 : ℝ)) : ℂ) * ((η ^ 2 : ℝ) : ℂ) = 1 := by
      push_cast
      field_simp
    have n2 : (((η⁻¹ ^ 2 : ℝ)) : ℂ) * ((η ^ 3 : ℝ) : ℂ) = ((η : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [smul_add, smul_smul, smul_smul, n1, n2, one_smul]
    abel
  have f3 : gt = Q *ᵥ x - G *ᵥ y' := by
    rw [hgt, e3, hz, hG, hy']
    simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]
    have n1 : ((η : ℝ) : ℂ) * ((η⁻¹ : ℝ) : ℂ) = 1 := by
      push_cast
      field_simp
    have e : ((η : ℝ) : ℂ) • (((η⁻¹ : ℝ) : ℂ) • (Q *ᵥ x)) = Q *ᵥ x := by
      rw [smul_smul, n1, one_smul]
    rw [smul_sub, smul_add, e]
    module
  obtain ⟨hx, hyw⟩ := saddle_elimination Xi Z hZ Q Qt G Ni hNi x ft y' gt f1 f3
  have nft : vnorm ft ≤ η⁻¹ ^ 2 * vnorm w := by
    rw [hft, vnorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left nf (by positivity)
  have ngt : vnorm gt ≤ η * (1 + a⁻¹ * bm) * vnorm w := by
    have h1 : vnorm (((a⁻¹ : ℝ) : ℂ) • (Mn *ᵥ h)) ≤ a⁻¹ * (bm * vnorm w) := by
      rw [vnorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (vnorm_mulVec_le _ _).trans (mul_le_mul hbm nh (vnorm_nonneg _) hbm0)
    rw [hgt, vnorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    have h2 := vnorm_sub_le g (((a⁻¹ : ℝ) : ℂ) • (Mn *ᵥ h))
    have h3 : vnorm (g - ((a⁻¹ : ℝ) : ℂ) • (Mn *ᵥ h)) ≤ (1 + a⁻¹ * bm) * vnorm w := by
      linarith
    calc _ ≤ η * ((1 + a⁻¹ * bm) * vnorm w) := mul_le_mul_of_nonneg_left h3 hη.le
      _ = _ := by ring
  have nqz : vnorm (Q *ᵥ (Z *ᵥ ft)) ≤ bq * (bz * (η⁻¹ ^ 2 * vnorm w)) := by
    refine (vnorm_mulVec_le _ _).trans (mul_le_mul hbq ?_ (vnorm_nonneg _) hbq0)
    exact (vnorm_mulVec_le _ _).trans (mul_le_mul hbz nft (vnorm_nonneg _) hbz0)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = bn * (η * (1 + a⁻¹ * bm) + 2 * (bq * (bz * η⁻¹ ^ 2))) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by
    rw [hY]
    positivity
  have nyw : vnorm (Sum.elim y' (-(Q *ᵥ x))) ≤ Y * vnorm w := by
    rw [hyw]
    refine (vnorm_mulVec_le _ _).trans ?_
    have h1 := vnorm_elim_le (gt - Q *ᵥ (Z *ᵥ ft)) (-(Q *ᵥ (Z *ᵥ ft)))
    rw [vnorm_neg] at h1
    have h2 := vnorm_sub_le gt (Q *ᵥ (Z *ᵥ ft))
    have h3 : vnorm (Sum.elim (gt - Q *ᵥ (Z *ᵥ ft)) (-(Q *ᵥ (Z *ᵥ ft)))) ≤
        (η * (1 + a⁻¹ * bm) + 2 * (bq * (bz * η⁻¹ ^ 2))) * vnorm w := by
      have e : (η * (1 + a⁻¹ * bm) + 2 * (bq * (bz * η⁻¹ ^ 2))) * vnorm w =
          η * (1 + a⁻¹ * bm) * vnorm w + 2 * (bq * (bz * (η⁻¹ ^ 2 * vnorm w))) := by ring
      rw [e]
      linarith
    calc _ ≤ bn * ((η * (1 + a⁻¹ * bm) + 2 * (bq * (bz * η⁻¹ ^ 2))) * vnorm w) :=
          mul_le_mul hbn h3 (vnorm_nonneg _) hbn0
      _ = _ := by rw [hY]; ring
  have ny' : vnorm y' ≤ Y * vnorm w :=
    (vnorm_comp_inl_le (Sum.elim y' (-(Q *ᵥ x)))).trans nyw
  have nqx : vnorm (-(Q *ᵥ x)) ≤ Y * vnorm w :=
    (vnorm_comp_inr_le (Sum.elim y' (-(Q *ᵥ x)))).trans nyw
  have ny : vnorm y ≤ η⁻¹ * (Y * vnorm w) := by
    have e : y = ((η⁻¹ : ℝ) : ℂ) • y' := by
      rw [hy', smul_smul]
      have n1 : ((η⁻¹ : ℝ) : ℂ) * ((η : ℝ) : ℂ) = 1 := by
        push_cast
        field_simp
      rw [n1, one_smul]
    rw [e, vnorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left ny' (by positivity)
  have nx : vnorm x ≤ bz * (η⁻¹ ^ 2 + 2 * bq * Y) * vnorm w := by
    rw [hx]
    refine (vnorm_mulVec_le _ _).trans ?_
    have h1 := vnorm_sub_le (ft - Qt *ᵥ (-(Q *ᵥ x))) (Qt *ᵥ y')
    have h2 := vnorm_sub_le ft (Qt *ᵥ (-(Q *ᵥ x)))
    have h3 : vnorm (Qt *ᵥ (-(Q *ᵥ x))) ≤ bq * (Y * vnorm w) :=
      (vnorm_mulVec_le _ _).trans (mul_le_mul hbq' nqx (vnorm_nonneg _) hbq0)
    have h4 : vnorm (Qt *ᵥ y') ≤ bq * (Y * vnorm w) :=
      (vnorm_mulVec_le _ _).trans (mul_le_mul hbq' ny' (vnorm_nonneg _) hbq0)
    have h5 : vnorm (ft - Qt *ᵥ (-(Q *ᵥ x)) - Qt *ᵥ y') ≤ (η⁻¹ ^ 2 + 2 * bq * Y) * vnorm w := by
      have e : (η⁻¹ ^ 2 + 2 * bq * Y) * vnorm w =
          η⁻¹ ^ 2 * vnorm w + bq * (Y * vnorm w) + bq * (Y * vnorm w) := by ring
      rw [e]
      linarith
    calc _ ≤ bz * ((η⁻¹ ^ 2 + 2 * bq * Y) * vnorm w) := mul_le_mul hbz h5 (vnorm_nonneg _) hbz0
      _ = _ := by ring
  have nz : vnorm z ≤ a⁻¹ * (1 + bm * (η⁻¹ * Y)) * vnorm w := by
    rw [hz, vnorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := vnorm_sub_le h (Mn.transpose *ᵥ y)
    have h2 : vnorm (Mn.transpose *ᵥ y) ≤ bm * (η⁻¹ * (Y * vnorm w)) :=
      (vnorm_mulVec_le _ _).trans (mul_le_mul hbm' ny (vnorm_nonneg _) hbm0)
    have h3 : vnorm (h - Mn.transpose *ᵥ y) ≤ (1 + bm * (η⁻¹ * Y)) * vnorm w := by
      have e : (1 + bm * (η⁻¹ * Y)) * vnorm w = vnorm w + bm * (η⁻¹ * (Y * vnorm w)) := by ring
      rw [e]
      linarith
    calc _ ≤ a⁻¹ * ((1 + bm * (η⁻¹ * Y)) * vnorm w) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have hfin : vnorm v ≤ vnorm x + vnorm z + vnorm y := by
    rw [hv]
    refine (vnorm_elim_le _ _).trans ?_
    have := vnorm_elim_le x z
    linarith
  have e : saddleConstant a η bz bq bn bm * vnorm w = bz * (η⁻¹ ^ 2 + 2 * bq * Y) * vnorm w +
      a⁻¹ * (1 + bm * (η⁻¹ * Y)) * vnorm w + η⁻¹ * (Y * vnorm w) := by
    rw [hY]
    unfold saddleConstant
    ring
  rw [e]
  linarith
end Saddle
private theorem complexMatrixOfLinearMap_eq {V V' I T : Type} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V'] [Fintype I] [DecidableEq I] [Fintype T]
    (Φ : V ≃ₗ[ℝ] (I → ℝ)) (Φ' : V' ≃ₗ[ℝ] (T → ℝ)) (f : V →ₗ[ℝ] V') (A : Matrix T I ℂ)
    (h : ∀ x t, ((Φ' (f x) t : ℝ) : ℂ) = ∑ κ, A t κ * ((Φ x κ : ℝ) : ℂ)) :
    complexMatrixOfLinearMap Φ Φ' f = A := by
  ext t κ
  simp only [complexMatrixOfLinearMap, Matrix.map_apply, LinearMap.toMatrix'_apply]
  have h1 := h (Φ.symm (Pi.single κ 1)) t
  rw [LinearEquiv.apply_symm_apply] at h1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h1, Finset.sum_eq_single κ]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro hκ
    exact absurd (Finset.mem_univ _) hκ
variable {L n k j : ℕ}
private theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem pauliCoeff_smul_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (z : ℂ) (a : Fin 3) :
    pauliCoeff a (z • X + Y) = z * pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.pauliCoeff_smul_add <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem halfTrace_mul_self {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (X * X) = ∑ a, pauliCoeff a X * pauliCoeff a X := by
  have key : ∀ x : Fin 3 → ℂ, ComplexMatrix2.halfTrace
      ((!![x 2, x 0 - Complex.I * x 1; x 0 + Complex.I * x 1, -x 2] : ComplexMatrix2) *
        !![x 2, x 0 - Complex.I * x 1; x 0 + Complex.I * x 1, -x 2]) = ∑ a, x a * x a := by
    intro x
    have hI := Complex.I_mul_I
    simp only [ComplexMatrix2.halfTrace, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]
    simp
    linear_combination (-(x 1 * x 1)) * hI
  have eX := sum_pauliCoeff_smul hX
  rw [ComplexMatrix2.sum_smul_pauliFamily] at eX
  rw [← key (fun a => pauliCoeff a X), eX]
abbrev _root_.YangMills.SharedProofs.p101009 := @halfTrace_mul_self
variable {L n k j : ℕ}
private theorem ofCoeffs_coeffs
    (hX : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    (edgePauliCoordinates L n k j).ofCoeffs ((edgePauliCoordinates L n k j).coeffs B) = B := by
  classical
  funext b
  change extendOddly (fun b => if h : b.IsPositivelyOriented then
    ofPauliCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) ⟨b, h⟩ else 0) b = B b
  have pos : ∀ b : PositiveEdge L n k j,
      ofPauliCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) b = B b.1 := fun b =>
    sum_pauliCoeff_smul (hB.1 b.1 b.2)
  simp only [extendOddly]
  rcases hX b with ⟨hp, hn⟩ | ⟨hp, hn⟩
  · rw [if_pos hp, dif_pos hp, pos ⟨b, hp⟩]
  · rw [if_neg hn, dif_pos hp, pos ⟨b.opposite, hp⟩, hB.2 b, neg_neg]
abbrev _root_.YangMills.SharedProofs.p21342 := @ofCoeffs_coeffs
private theorem toPauliCoeffs_smul_add {A B : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n k j) (hB : B ∈ complexEdgeForms L n k j) (z : ℂ)
    (t : Fin 3 × PositiveEdge L n k j) :
    toPauliCoeffs (restrictToPositiveEdges (z • A + B)) t =
      z * toPauliCoeffs (restrictToPositiveEdges A) t + toPauliCoeffs (restrictToPositiveEdges B) t :=
  pauliCoeff_smul_add (hA.1 _ t.2.2) (hB.1 _ t.2.2) z t.1
private theorem toPauliCoeffs_zero (t : Fin 3 × PositiveEdge L n k j) :
    toPauliCoeffs (restrictToPositiveEdges (0 : Edge L n k j → ComplexMatrix2)) t = 0 :=
  pauliCoeff_zero t.1
private theorem tangentForms_of_quiet (U : Edge L n k 0 → ComplexMatrix2) (ξ : LevelForms L n k)
    (h : ∀ i, ξ.2 i = 0) (j : ℕ) : tangentForms U ξ j = meanCovariant U j ξ.1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change meanCovariantStep (meanIterate U j) (tangentForms U ξ j) +
      (if h' : j < k then _ else _) = meanCovariantStep (meanIterate U j) (meanCovariant U j ξ.1)
    rw [ih]
    split_ifs with h'
    · rw [h ⟨j, h'⟩]
      simp
    · simp
abbrev _root_.YangMills.SharedProofs.p88273 := @tangentForms_of_quiet
private theorem eq_of_symm_of_quadratic {E K : Type} [AddCommGroup E] [Module ℝ E] [Fintype K]
    (Φ : E ≃ₗ[ℝ] (K → ℝ)) (S S' : E →ₗ[ℝ] E)
    (hS : ∀ x y, ∑ κ, Φ x κ * Φ (S y) κ = ∑ κ, Φ (S x) κ * Φ y κ)
    (hS' : ∀ x y, ∑ κ, Φ x κ * Φ (S' y) κ = ∑ κ, Φ (S' x) κ * Φ y κ)
    (hq : ∀ x, ∑ κ, Φ x κ * Φ (S x) κ = ∑ κ, Φ x κ * Φ (S' x) κ) : S = S' := by
  have hpol : ∀ (R : E →ₗ[ℝ] E), (∀ x y, ∑ κ, Φ x κ * Φ (R y) κ = ∑ κ, Φ (R x) κ * Φ y κ) →
      ∀ x y, 2 * ∑ κ, Φ x κ * Φ (R y) κ = ∑ κ, Φ (x + y) κ * Φ (R (x + y)) κ -
        ∑ κ, Φ x κ * Φ (R x) κ - ∑ κ, Φ y κ * Φ (R y) κ := by
    intro R hR x y
    have h1 : ∑ κ, Φ y κ * Φ (R x) κ = ∑ κ, Φ x κ * Φ (R y) κ := by
      rw [hR y x]
      exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
    simp only [map_add, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    rw [h1]
    ring
  have hxy : ∀ x y, ∑ κ, Φ x κ * Φ (S y) κ = ∑ κ, Φ x κ * Φ (S' y) κ := by
    intro x y
    have h1 := hpol S hS x y
    have h2 := hpol S' hS' x y
    rw [hq, hq x, hq y] at h1
    linarith
  refine LinearMap.ext fun y => Φ.injective ?_
  have h3 := hxy (S y - S' y) y
  have h4 : ∑ κ, Φ (S y - S' y) κ * Φ (S y - S' y) κ = 0 := by
    simp only [map_sub, Pi.sub_apply]
    simp only [map_sub, Pi.sub_apply] at h3
    rw [← sub_eq_zero] at h3
    rw [← h3, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun κ _ => by ring
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun κ _ => mul_self_nonneg _).1 h4
  funext κ
  have h6 := mul_self_eq_zero.1 (h5 κ (Finset.mem_univ κ))
  simp only [map_sub, Pi.sub_apply] at h6
  linarith
abbrev _root_.YangMills.SharedProofs.p2931 := @eq_of_symm_of_quadratic
private theorem traceFinsumPairing_zero_left {ι : Type*} (f : ι → ComplexMatrix2) :
    Tower.traceFinsumPairing (0 : ι → ComplexMatrix2) f = 0 := by
  simp [Tower.traceFinsumPairing, ComplexMatrix2.halfTrace]
private theorem blocks_near_identity (h₂ : PauliCoordsOrthonormal)
    (h₃ : BackgroundHessianMatrix) (h₄ : ShiftedGaugeMapAtQuietPoint)
    (h₅ : NoiseCovarianceAsPlainChainSum) (h₆ : MeanKernelsRepresent)
    (h₇ : ChainActionHessianAtQuiet) (h₈ : MeanDerivOnForms.Claim)
    (h₉ : MeanIteratesTendToOne)
    (h₁₀ : Tower.RealQuadraticTransposes.Statement)
    {a : ℝ} (ha : 0 < a) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    [∀ j, Fintype (PositiveEdge L n k j)]
    [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
    [DecidableEq (LevelFormIndex L n k)]
    [DecidableEq (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))]
    [Fintype (GhostCoordIndex L n k)] [Fintype (Fin 3 × Vertex L n k 0)]
    [Fintype (Fin 3 × Vertex L n k k)] :
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      ∃ Mn : Matrix (Fin 3 × PositiveEdge L n k k)
          (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) ℂ,
        (Matrix.of (noiseCovariance a L n k U k) : Matrix (Fin 3 × PositiveEdge L n k k)
            (Fin 3 × PositiveEdge L n k k) ℂ) =
          ((Mn * (Matrix.diagonal (fun κ : Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1) =>
            (((a * (meanRadius (meanIterate U κ.1) κ.2.2.1).re : ℝ) : ℂ))⁻¹) :
              Matrix (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))
                (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) ℂ) :
            Matrix (Fin 3 × PositiveEdge L n k k)
              (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) ℂ) * Mn.transpose :
            Matrix (Fin 3 × PositiveEdge L n k k) (Fin 3 × PositiveEdge L n k k) ℂ) ∧
        ∀ P : PauliCoordinates L n k,
          complexMatrixOfLinearMap P.formCoords P.formCoords (gaugedOperator a (quietPoint U) 0 0) =
            fromBlocks (fun ι ι' => ((finestMesh L k ^ 2 : ℝ) : ℂ) * (rescaledOperators L n k U).X ι ι')
              0 0 (Matrix.diagonal fun κ =>
                ((a * (meanRadius (meanIterate U κ.1) κ.2.2.1).re : ℝ) : ℂ)) ∧
          complexMatrixOfLinearMap P.formCoords P.topFormCoords (shiftedGaugeMap (quietPoint U)) =
            fromCols (((finestMesh L k : ℝ) : ℂ)⁻¹ • Matrix.of (meanKernelQ L n k U)) Mn := by
  classical
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  haveI : NeZero L := ⟨by omega⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hX : ∀ i, i ≤ k → ∀ b : Edge L n k i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun i hi b =>
    PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) b
  obtain ⟨Ψ₀, hΨ₀, hp₀⟩ := (h₂ L n k 0 hL hn (Nat.zero_le _)).1
  obtain ⟨ΨT, hΨT, hpT⟩ := (h₂ L n k k hL hn le_rfl).1
  have hc : ∀ i : Fin k, ∃ Ψ : edgeFormSpace L n k (i + 1) ≃ₗ[ℝ]
      (Fin 3 × PositiveEdge L n k (i + 1) → ℝ),
      (∀ (f : edgeFormSpace L n k (i + 1)) ι, toPauliCoeffs (restrictToPositiveEdges
        (f : Edge L n k (i + 1) → ComplexMatrix2)) ι = ((Ψ f ι : ℝ) : ℂ)) ∧
      ∀ f g : edgeFormSpace L n k (i + 1), edgeFormPairing (f : Edge L n k (i + 1) → ComplexMatrix2)
        (g : Edge L n k (i + 1) → ComplexMatrix2) = ((∑ ι, Ψ f ι * Ψ g ι : ℝ) : ℂ) := fun i =>
    (h₂ L n k (i + 1) hL hn i.2).1
  choose Ψ hΨ hp using hc
  let Φ : LevelForms L n k ≃ₗ[ℝ]
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ) :=
    { toFun := fun ξ => Sum.elim (Ψ₀ ξ.1) fun κ => Ψ κ.1 (ξ.2 κ.1) κ.2
      map_add' := fun ξ ξ' => by
        funext κ
        rcases κ with ι | κ <;> simp
      map_smul' := fun r ξ => by
        funext κ
        rcases κ with ι | κ <;> simp
      invFun := fun y => (Ψ₀.symm fun ι => y (.inl ι), fun i => (Ψ i).symm fun ι => y (.inr ⟨i, ι⟩))
      left_inv := fun ξ => by
        refine Prod.ext ?_ (funext fun i => ?_)
        · exact Ψ₀.symm_apply_apply ξ.1
        · exact (Ψ i).symm_apply_apply (ξ.2 i)
      right_inv := fun y => by
        funext κ
        rcases κ with ι | ⟨i, ι⟩ <;> simp }
  have hΦl : ∀ ξ ι, Φ ξ (.inl ι) = Ψ₀ ξ.1 ι := fun _ _ => rfl
  have hΦr : ∀ ξ κ, Φ ξ (.inr κ) = Ψ κ.1 (ξ.2 κ.1) κ.2 := fun _ _ => rfl
  have hchain : ∀ ξ ξ' : LevelForms L n k, levelPairing (formValues ξ) (formValues ξ') =
      ∑ κ, Φ ξ κ * Φ ξ' κ := by
    intro ξ ξ'
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [levelPairing, formValues, hΦl, hΦr]
    congr 1
    · rw [hp₀]
      exact Complex.ofReal_re _
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp i]
      exact Complex.ofReal_re _
  set η : ℝ := finestMesh L k with hη
  have heta : 0 < η := zpow_pos hLpos _
  have hetaC : ((η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have htop : meshAt L k k = 1 := by
    change (L : ℝ) ^ ((k : ℤ) - (k : ℤ)) = 1
    simp
  have hev : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)), ∀ i ∈ Finset.range k,
      ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
        meanRadius (meanIterate U i) c = (((meanRadius (meanIterate U i) c).re : ℝ) : ℂ) ∧
          0 < (meanRadius (meanIterate U i) c).re := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    filter_upwards [(h₉ L hL k n hn i hik.le).eventually (h₈ L hL n k i hn hik)] with U f c hc
    exact ⟨(f.2.1 c hc).1, (f.2.1 c hc).2.1⟩
  have e₃ := h₃ L hL k n hk hn
  have e₄ := h₄ L hL k n hk hn
  have e₅ := h₅ a ha L hL k n hk hn
  have e₆ := h₆ L hL k n hk hn
  have e₇ := h₇ a L hL k n hn
  have e₉ := (h₁₀ L n k hL hn hk).2
  unfold EventuallyNearIdentity at e₃ e₄ e₅ e₆ e₇ e₉ ⊢
  filter_upwards [e₃, e₄, e₅, e₆, e₇, e₉, hev] with U f₃ f₄ f₅ f₆ f₇ f₉ f₈
  set p := rescaledOperators L n k U with hp
  have hptop : p.coarse = 1 := htop
  have hpη : p.eta = η := rfl
  set X := quietPoint U with hXdef
  let r : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ := fun κ =>
    (meanRadius (meanIterate U κ.1) κ.2.2.1).re
  have hr : ∀ κ, 0 < r κ := fun κ =>
    (f₈ κ.1 (Finset.mem_range.2 κ.1.2) κ.2.2.1 κ.2.2.2).2
  let d : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ := fun κ => a * r κ
  have hd : ∀ κ, 0 < d κ := fun κ => mul_pos ha (hr κ)
  obtain ⟨T₁, hT₁, -⟩ := f₉.2.2.existsUnique_hessian 0 0
  have hXop : IsBackgroundHessian U 0 0 (backgroundHessian U 0 0) :=
    Classical.epsilon_spec (p := IsBackgroundHessian U 0 0) ⟨T₁, hT₁⟩
  set Xop := backgroundHessian U 0 0 with hXopdef
  let A : (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ) →ₗ[ℝ]
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ) :=
    { toFun := fun y => Sum.elim (Ψ₀ (Xop (Ψ₀.symm fun ι => y (.inl ι)))) fun κ => d κ * y (.inr κ)
      map_add' := fun y y' => by
        funext κ
        rcases κ with ι | κ
        · have : (fun ι => (y + y') (.inl ι)) = (fun ι => y (.inl ι)) + fun ι => y' (.inl ι) := rfl
          change Ψ₀ (Xop (Ψ₀.symm fun ι => (y + y') (.inl ι))) ι =
            Ψ₀ (Xop (Ψ₀.symm fun ι => y (.inl ι))) ι + Ψ₀ (Xop (Ψ₀.symm fun ι => y' (.inl ι))) ι
          rw [this, map_add, map_add, map_add]
          rfl
        · simp only [Sum.elim_inr, Pi.add_apply, mul_add]
      map_smul' := fun c y => by
        funext κ
        rcases κ with ι | κ
        · have : (fun ι => (c • y) (.inl ι)) = c • fun ι => y (.inl ι) := rfl
          change Ψ₀ (Xop (Ψ₀.symm fun ι => (c • y) (.inl ι))) ι =
            c • Ψ₀ (Xop (Ψ₀.symm fun ι => y (.inl ι))) ι
          rw [this, map_smul, map_smul, map_smul]
          rfl
        · simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }
  let T₀ : LevelForms L n k →ₗ[ℝ] LevelForms L n k :=
    Φ.symm.toLinearMap ∘ₗ A ∘ₗ Φ.toLinearMap
  have hT₀ : ∀ ξ, Φ (T₀ ξ) = A (Φ ξ) := fun ξ => by simp [T₀]
  have hT₀l : ∀ ξ ι, Φ (T₀ ξ) (.inl ι) = Ψ₀ (Xop ξ.1) ι := by
    intro ξ ι
    rw [hT₀]
    change Ψ₀ (Xop (Ψ₀.symm fun ι => Ψ₀ ξ.1 ι)) ι = _
    simp
  have hT₀r : ∀ ξ κ, Φ (T₀ ξ) (.inr κ) = d κ * Φ ξ (.inr κ) := by
    intro ξ κ
    rw [hT₀]
    rfl
  have hsym₀ : ∀ B B' : edgeFormSpace L n k 0,
      ∑ ι, Ψ₀ B ι * Ψ₀ (Xop B') ι = ∑ ι, Ψ₀ (Xop B) ι * Ψ₀ B' ι := by
    intro B B'
    have := hXop.1 B B'
    rw [hp₀, hp₀] at this
    exact Complex.ofReal_injective this
  have hform₀ : ∀ B : edgeFormSpace L n k 0,
      ∑ ι, Ψ₀ B ι * Ψ₀ (Xop B) ι = backgroundHessianForm U 0 0 B := by
    intro B
    have := hXop.2 B
    rw [hp₀] at this
    exact Complex.ofReal_injective this
  have hzeroL : ∀ y : LevelValues L n k, levelPairing (formValues (0 : LevelForms L n k)) y = 0 := by
    intro y
    have h0 : ∀ {i : ℕ} (g : Edge L n k i → ComplexMatrix2),
        (edgeFormPairing (0 : Edge L n k i → ComplexMatrix2) g).re = 0 := by
      intro i g
      have : edgeFormPairing (0 : Edge L n k i → ComplexMatrix2) g = 0 :=
        traceFinsumPairing_zero_left _
      rw [this]
      rfl
    simp only [levelPairing, formValues]
    have e1 : ((0 : LevelForms L n k).1 : Edge L n k 0 → ComplexMatrix2) = 0 := rfl
    have e2 : ∀ i : Fin k, ((0 : LevelForms L n k).2 i : Edge L n k (i + 1) → ComplexMatrix2) = 0 :=
      fun _ => rfl
    simp only [e1, e2, h0, Finset.sum_const_zero, add_zero]
  have hbq : ∀ B : edgeFormSpace L n k 0, backgroundHessianForm U 0 0 B =
      Tower.leftSecondDeriv (plaquetteAction L n k) U B B +
        traceFinsumNorm (gaugeSliceResidual U B : Vertex L n k 0 → ComplexMatrix2) ^ 2 := by
    intro B
    have h1 : sourceQuadraticForm U 0 0 B = 0 := by
      have h0 : ∀ g : Edge L n k 0 → ComplexMatrix2,
          (edgeFormPairing (((0 : edgeFormSpace L n k 0)) : Edge L n k 0 → ComplexMatrix2) g).re = 0 := by
        intro g
        have : edgeFormPairing ((0 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) g = 0 :=
          traceFinsumPairing_zero_left _
        rw [this]
        rfl
      have h2 : ∀ g : PositiveEdge L n k k → ComplexMatrix2,
          (Tower.traceFinsumPairing (restrictToPositiveEdges
            ((0 : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2)) g).re = 0 := by
        intro g
        have : Tower.traceFinsumPairing (restrictToPositiveEdges
            ((0 : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2)) g = 0 :=
          traceFinsumPairing_zero_left _
        rw [this]
        rfl
      simp only [sourceQuadraticForm, h0, h2, mul_zero, add_zero, sub_zero]
    simp only [backgroundHessianForm, h1, add_zero]
  have hmem : ∀ ξ : LevelForms L n k, gaugedRightValue a X 0 0 ξ =
      RunningCouplingSlope.leftSecondDeriv (chainAction a) X ξ ξ +
        traceFinsumNorm (gaugeSliceResidual U ξ.1 : Vertex L n k 0 → ComplexMatrix2) ^ 2 := by
    intro ξ
    have h2 : ∀ g : PositiveEdge L n k k → ComplexMatrix2,
        (Tower.traceFinsumPairing (restrictToPositiveEdges
          ((0 : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2)) g).re = 0 := by
      intro g
      have : Tower.traceFinsumPairing (restrictToPositiveEdges
          ((0 : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2)) g = 0 :=
        traceFinsumPairing_zero_left _
      rw [this]
      rfl
    simp only [gaugedRightValue, gaugedFormValue, hzeroL, h2, mul_zero, add_zero, sub_zero]
    rfl
  have hnoise : ∀ ξ : LevelForms L n k, a * ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
      (meanRadius (meanIterate U i) c.1).re *
        (ComplexMatrix2.halfTrace
          (((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1 *
          ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1)).re =
      ∑ κ, Φ ξ (.inr κ) * (d κ * Φ ξ (.inr κ)) := by
    intro ξ
    rw [Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hsl : ((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1 ∈
        ComplexMatrix2.traceless :=
      ((ξ.2 i).2.1 c.1 c.2).2
    have hco : ∀ a' : Fin 3, pauliCoeff a'
        (((ξ.2 i : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c.1) =
        ((Ψ i (ξ.2 i) (a', c) : ℝ) : ℂ) := fun a' => hΨ i (ξ.2 i) (a', c)
    rw [halfTrace_mul_self hsl]
    simp only [hco]
    have e : (∑ a' : Fin 3, ((Ψ i (ξ.2 i) (a', c) : ℝ) : ℂ) * ((Ψ i (ξ.2 i) (a', c) : ℝ) : ℂ)).re =
        ∑ a' : Fin 3, Ψ i (ξ.2 i) (a', c) * Ψ i (ξ.2 i) (a', c) := by
      rw [← Complex.ofReal_re (∑ a' : Fin 3, Ψ i (ξ.2 i) (a', c) * Ψ i (ξ.2 i) (a', c))]
      push_cast
      rfl
    rw [e, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    change a * ((meanRadius (meanIterate U i) c.1).re * _) =
      _ * (a * (meanRadius (meanIterate U i) c.1).re * _)
    rw [hΦr]
    ring
  have hsoft₀ : IsGaugedOperator a X 0 0 T₀ := by
    refine ⟨fun ξ ξ' => ?_, fun ξ => ?_⟩
    · rw [hchain, hchain, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [hT₀l, hT₀r, hΦl]
      rw [hsym₀]
      congr 1
      exact Finset.sum_congr rfl fun κ _ => by ring
    · rw [hchain, Fintype.sum_sum_type, hmem, f₇ ξ, hnoise]
      simp only [hT₀l, hT₀r, hΦl]
      rw [hform₀, hbq]
      ring
  have hsoft : IsGaugedOperator a X 0 0 (gaugedOperator a X 0 0) :=
    Classical.epsilon_spec (p := IsGaugedOperator a X 0 0) ⟨T₀, hsoft₀⟩
  have hTeq : gaugedOperator a X 0 0 = T₀ := by
    refine eq_of_symm_of_quadratic Φ _ _ (fun x y => ?_) (fun x y => ?_) fun x => ?_
    · rw [← hchain, ← hchain]
      exact hsoft.1 x y
    · rw [← hchain, ← hchain]
      exact hsoft₀.1 x y
    · rw [← hchain, ← hchain, hsoft.2 x, hsoft₀.2 x]
  set M := shiftedGaugeMap X with hMdef
  have hMv : ∀ ξ, (M ξ : Edge L n k k → ComplexMatrix2) = tangentForms U ξ k := fun ξ => (f₄ ξ).2
  obtain ⟨-, fQ, -, fre, -, -, -⟩ := f₆
  let Qs : Matrix (Fin 3 × PositiveEdge L n k k) (Fin 3 × PositiveEdge L n k 0) ℂ :=
    ((η : ℂ))⁻¹ • Matrix.of (meanKernelQ L n k U)
  let Mn : Matrix (Fin 3 × PositiveEdge L n k k) (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) ℂ :=
    fun t κ => ((ΨT (M (Φ.symm (Pi.single (.inr κ) 1))) t : ℝ) : ℂ)
  have hQs : ∀ ι t, ((ΨT (M (Φ.symm (Pi.single (.inl ι) 1))) t : ℝ) : ℂ) = Qs t ι := by
    intro ι t
    set ξ := Φ.symm (Pi.single (.inl ι) 1) with hξ
    have hno : ∀ i, ξ.2 i = 0 := by
      intro i
      change (Ψ i).symm (fun ι' => (Pi.single (.inl ι) (1 : ℝ) :
        (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
          (.inr ⟨i, ι'⟩)) = 0
      have : (fun ι' => (Pi.single (.inl ι) (1 : ℝ) :
        (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
          (.inr ⟨i, ι'⟩)) = 0 := by
        funext ι'
        simp
      rw [this, map_zero]
    have hB : (ξ.1 : Edge L n k 0 → ComplexMatrix2) ∈ edgeFormSpace L n k 0 := ξ.1.2
    have hBc : (ξ.1 : Edge L n k 0 → ComplexMatrix2) ∈ complexEdgeForms L n k 0 :=
      ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
    have hcoef : ∀ ι', toPauliCoeffs (restrictToPositiveEdges (ξ.1 : Edge L n k 0 → ComplexMatrix2)) ι' =
        if ι' = ι then 1 else 0 := by
      intro ι'
      rw [hΨ₀, ← hΦl, hξ, LinearEquiv.apply_symm_apply]
      by_cases h : ι' = ι
      · rw [if_pos h, h]
        simp
      · simp [h]
    have g := congrFun (fQ (toPauliCoeffs (restrictToPositiveEdges
      (ξ.1 : Edge L n k 0 → ComplexMatrix2)))).2 t
    change applyKernel (meanKernelQ L n k U) (toPauliCoeffs (restrictToPositiveEdges
      (ξ.1 : Edge L n k 0 → ComplexMatrix2))) t = toPauliCoeffs (restrictToPositiveEdges (finestMesh L k •
        meanCovariant U k ((edgePauliCoordinates L n k 0).ofCoeffs ((edgePauliCoordinates L n k 0).coeffs
          (ξ.1 : Edge L n k 0 → ComplexMatrix2))))) t at g
    rw [ofCoeffs_coeffs (hX 0 (Nat.zero_le _)) hBc] at g
    have hm : meanCovariant U k (ξ.1 : Edge L n k 0 → ComplexMatrix2) ∈ edgeFormSpace L n k k :=
      fre k le_rfl _ hB
    have hmc : meanCovariant U k (ξ.1 : Edge L n k 0 → ComplexMatrix2) ∈ complexEdgeForms L n k k :=
      ⟨fun b hb => (hm.1 b hb).2, hm.2⟩
    have e : finestMesh L k • meanCovariant U k (ξ.1 : Edge L n k 0 → ComplexMatrix2) =
        ((η : ℝ) : ℂ) • meanCovariant U k (ξ.1 : Edge L n k 0 → ComplexMatrix2) + 0 := by
      rw [add_zero]
      funext b
      exact (Complex.coe_smul _ _).symm
    rw [e, toPauliCoeffs_smul_add hmc (complexEdgeForms L n k k).zero_mem, toPauliCoeffs_zero,
      add_zero] at g
    simp only [applyKernel, tsum_fintype, hcoef, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at g
    have hMξ : (M ξ : Edge L n k k → ComplexMatrix2) =
        meanCovariant U k (ξ.1 : Edge L n k 0 → ComplexMatrix2) := by
      rw [hMv, tangentForms_of_quiet U ξ hno]
    change _ = ((η : ℂ))⁻¹ * meanKernelQ L n k U t ι
    rw [g, ← hΨT, hMξ]
    field_simp
  have hMact : ∀ (x : LevelForms L n k) t, ((ΨT (M x) t : ℝ) : ℂ) =
      ∑ κ, (fromCols Qs Mn) t κ * ((Φ x κ : ℝ) : ℂ) := by
    intro x t
    let Lm : (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ)
        →ₗ[ℝ] (Fin 3 × PositiveEdge L n k k → ℝ) :=
      ΨT.toLinearMap ∘ₗ M ∘ₗ Φ.symm.toLinearMap
    have h1 := congrFun (LinearMap.toMatrix'_mulVec Lm (Φ x)) t
    have h2 : Lm (Φ x) t = ΨT (M x) t := by simp [Lm]
    rw [← h2, ← h1]
    simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    congr 1
    rw [LinearMap.toMatrix'_apply]
    rcases κ with ι | κ
    · rw [fromCols_apply_inl, ← hQs]
      rfl
    · rw [fromCols_apply_inr]
      rfl
  let E : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → LevelForms L n k := fun κ =>
    Φ.symm (Pi.single (.inr κ) 1)
  have hE0 : ∀ κ, (E κ).1 = 0 := by
    intro κ
    change Ψ₀.symm (fun ι => (Pi.single (.inr κ) (1 : ℝ) :
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
        (.inl ι)) = 0
    have : (fun ι => (Pi.single (.inr κ) (1 : ℝ) :
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
        (.inl ι)) = 0 := by
      funext ι
      simp
    rw [this, map_zero]
  have hE1 : ∀ κ i, i ≠ κ.1 → (E κ).2 i = 0 := by
    intro κ i hi
    change (Ψ i).symm (fun ι => (Pi.single (.inr κ) (1 : ℝ) :
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
        (.inr ⟨i, ι⟩)) = 0
    have : (fun ι => (Pi.single (.inr κ) (1 : ℝ) :
      (Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) → ℝ))
        (.inr ⟨i, ι⟩)) = 0 := by
      funext ι
      refine Pi.single_eq_of_ne (fun h => ?_) _
      exact hi (Sigma.mk.inj (Sum.inr.inj h)).1
    rw [this, map_zero]
  have hE2 : ∀ κ ι, toPauliCoeffs (restrictToPositiveEdges
      (((E κ).2 κ.1 : edgeFormSpace L n k (κ.1 + 1)) : Edge L n k (κ.1 + 1) → ComplexMatrix2)) ι =
        if ι = κ.2 then 1 else 0 := by
    rintro ⟨i, ι₀⟩ ι
    rw [hΨ i]
    change (((Φ (E ⟨i, ι₀⟩) (.inr ⟨i, ι⟩) : ℝ)) : ℂ) = _
    simp only [E, LinearEquiv.apply_symm_apply]
    by_cases h : ι = ι₀
    · rw [if_pos h, h]
      simp
    · have h' : (Sum.inr ⟨i, ι⟩ : Fin 3 × PositiveEdge L n k 0 ⊕
          (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))) ≠ .inr ⟨i, ι₀⟩ := by
        intro h2
        exact h (eq_of_heq (Sigma.mk.inj (Sum.inr.inj h2)).2)
      rw [Pi.single_eq_of_ne h', if_neg h]
      simp
  have hΓ := f₅ E hE0 hE1 hE2 k le_rfl
  have hMnco : ∀ κ t, toPauliCoeffs (restrictToPositiveEdges (tangentForms U (E κ) k)) t = Mn t κ := by
    intro κ t
    rw [← hMv]
    exact hΨT _ t
  have hΓm : Matrix.of (noiseCovariance a L n k U k) =
      Mn * diagonal (fun κ => (((d κ : ℝ) : ℂ))⁻¹) * Mn.transpose := by
    ext t t'
    rw [Matrix.of_apply, hΓ t t', finsum_eq_sum_of_fintype, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun κ _ => ?_
    have e : (((a * (meanRadius (meanIterate U κ.1) κ.2.2.1).re)⁻¹ : ℝ) : ℂ) =
        (((d κ : ℝ) : ℂ))⁻¹ := Complex.ofReal_inv _
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, hMnco, hMnco, e]
    ring
  let X' : Matrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × PositiveEdge L n k 0) ℂ :=
    fun ι ι' => ((η ^ 2 : ℝ) : ℂ) * p.X ι ι'
  let Dg : Matrix (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))
      (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) ℂ := diagonal fun κ => ((d κ : ℝ) : ℂ)
  have hXact : ∀ (x : LevelForms L n k)
      (κ : Fin 3 × PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1))),
      ((Φ (gaugedOperator a X 0 0 x) κ : ℝ) : ℂ) = ∑ κ', (fromBlocks X' 0 0 Dg) κ κ' *
          ((Φ x κ' : ℝ) : ℂ) := by
    intro x κ
    rw [hTeq, Fintype.sum_sum_type]
    rcases κ with ι | κ
    · have h₁' : ((Ψ₀ (Xop x.1) ι : ℝ) : ℂ) = ∑ j, X' ι j * ((Φ x (.inl j) : ℝ) : ℂ) := by
        rw [← hΨ₀, f₃ x.1 ι]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΨ₀, hΦl]
      have z : ∀ b, (fromBlocks X' 0 0 Dg) (.inl ι) (.inr b) * ((Φ x (.inr b) : ℝ) : ℂ) = 0 :=
        fun b => by
          change (0 : ℂ) * _ = 0
          exact zero_mul _
      rw [hT₀l, h₁']
      simp only [z, Finset.sum_const_zero, add_zero]
      rfl
    · have z : ∀ b, (fromBlocks X' 0 0 Dg) (.inr κ) (.inl b) * ((Φ x (.inl b) : ℝ) : ℂ) = 0 :=
        fun b => by
          change (0 : ℂ) * _ = 0
          exact zero_mul _
      rw [hT₀r]
      simp only [z, Finset.sum_const_zero, zero_add]
      rw [Finset.sum_eq_single κ (fun b _ hb => by
        change Dg κ b * _ = 0
        rw [show Dg κ b = 0 from diagonal_apply_ne _ (Ne.symm hb), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h)]
      change _ = Dg κ κ * _
      rw [show Dg κ κ = ((d κ : ℝ) : ℂ) from diagonal_apply_eq _ _]
      push_cast
      rfl
  refine ⟨Mn, hΓm, fun P => ?_⟩
  have hPΦ : P.formCoords = Φ := by
    refine LinearEquiv.ext fun ξ => funext fun κ => ?_
    apply Complex.ofReal_injective
    rcases κ with ι | ⟨i, ι⟩
    · rw [← P.formCoords_base, hΦl, hΨ₀]
    · rw [← P.formCoords_level, hΦr, hΨ]
  have hPT : P.topFormCoords = ΨT := by
    refine LinearEquiv.ext fun μ => funext fun t => ?_
    apply Complex.ofReal_injective
    rw [← P.topFormCoords_apply, hΨT]
  rw [hPΦ, hPT]
  exact ⟨complexMatrixOfLinearMap_eq _ _ _ _ hXact, complexMatrixOfLinearMap_eq _ _ _ _ hMact⟩
private theorem normalizedMean_one (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    normalizedMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1 :=
  (hD L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem c hc).2.2.1
private theorem meanRadius_one (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    meanRadius (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1 :=
  (hD L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem c hc).2.1
private theorem meanIterate_one (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : ∀ j, j ≤ k →
    meanIterate (trivialField L n k 0) j = fun _ => (1 : ComplexMatrix2)
  | 0, _ => rfl
  | j + 1, hj => by
    have hjk : j < k := hj
    have ih := meanIterate_one hD hL hn j hjk.le
    have e : meanIterate (trivialField L n k 0) (j + 1) = fieldOfPositiveValues
        fun c => (1 : ComplexMatrix2) * normalizedMean (meanIterate (trivialField L n k 0) j) c.1 := by
      show levelField _ (j + 1) = _
      rw [levelField, dif_pos hjk]
      rfl
    rw [e, ih]
    funext b
    unfold fieldOfPositiveValues
    split_ifs with h1 h2
    · simp [normalizedMean_one hD hL hn hjk h1]
    · simp [normalizedMean_one hD hL hn hjk h2]
    · rfl
private theorem twoSourceBackground_zero (L n k : ℕ) (z : Fin 4 → ℤ) :
    twoSourceBackground L n k z 0 0 = trivialField L n k 0 := by
  classical
  funext b
  simp only [twoSourceBackground, PeriodicLattice.expTwist, Complex.ofReal_zero, zero_smul,
    add_zero, Pi.zero_apply, smul_zero]
  have he : ComplexMatrix2.matExp (0 : ComplexMatrix2) = 1 := NormedSpace.exp_zero
  split_ifs <;> simp [he]
abbrev _root_.YangMills.SharedProofs.p56412 := @twoSourceBackground_zero
private theorem expMove_zero (L n k : ℕ) :
    expMove (0 : LevelForms L n k) (unitPoint L n k) =
      quietPoint (trivialField L n k 0) := by apply _root_.YangMills.DeltaSharedProofs.p500473 <;> assumption
private theorem finite_face [NeZero L] (j : ℕ) : Finite (Face L n k j) := by apply _root_.YangMills.SharedProofs.p23234 <;> assumption
private theorem transpose_eq_conjTranspose_of_real {A B : Type} (M : Matrix A B ℂ)
    (h : ∀ i j, (M i j).im = 0) : M.transpose = M.conjTranspose := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply]
  exact (Complex.conj_eq_iff_im.2 (h j i)).symm
private theorem of_compKernel {A B D : Type} [Fintype B] (X : A → B → ℂ) (Y : B → D → ℂ) :
    Matrix.of (compKernel X Y) = Matrix.of X * Matrix.of Y := by apply _root_.YangMills.DeltaSharedProofs.p17742 <;> assumption
end SaddleInverseAtIdentity
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 1600000 in
open SaddleInverseAtIdentity Tower PeriodicOperators Matrices in
theorem saddlePointMatrixInverseBounded_holds
    (hBd : LocalMatricesBoundedAndInverseLocal)
    (hF : FreeInversesLocal) (hR : PeriodicResolventSqrtsLocal)
    (hA : BackgroundMeansAreLocal)
    (hN : NoiseMatrixAtTrivialLocalInverse)
    (hNC : FlatNoiseCovariancePositive)
    (hD : NormalizedMeanAtOne)
    (h₂ : PauliCoordsOrthonormal)
    (h₃ : BackgroundHessianMatrix) (h₄ : ShiftedGaugeMapAtQuietPoint)
    (h₅ : NoiseCovarianceAsPlainChainSum) (h₆ : MeanKernelsRepresent)
    (h₇ : ChainActionHessianAtQuiet) (h₈ : MeanDerivOnForms.Claim)
    (h₉ : MeanIteratesTendToOne)
    (h₁₀ : Tower.RealQuadraticTransposes.Statement) :
    SaddlePointMatrixInverseBounded := by
  intro a ha L hL k hk
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  haveI : NeZero L := ⟨by omega⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  obtain ⟨M₁, θ₁, hM₁, hθ₁, hF'⟩ := hF L hL
  obtain ⟨M₂, θ₂, hM₂, hθ₂, hR'⟩ := hR L hL
  obtain ⟨M₃, θ₃, hM₃, hθ₃, hA'⟩ := hA a ha L hL
  obtain ⟨M₄, θ₄, hM₄, hθ₄, hN'⟩ := hN a ha L hL
  obtain ⟨hb, -⟩ := hBd
  obtain ⟨S₁, hS₁, hb₁⟩ := hb θ₁ hθ₁
  obtain ⟨S₂, hS₂, hb₂⟩ := hb θ₂ hθ₂
  obtain ⟨S₃, hS₃, hb₃⟩ := hb θ₃ hθ₃
  obtain ⟨S₄, hS₄, hb₄⟩ := hb θ₄ hθ₄
  obtain ⟨n₁, hF''⟩ := hF' k hk
  obtain ⟨n₂, hR''⟩ := hR' k hk
  obtain ⟨n₃, hA''⟩ := hA' k hk
  obtain ⟨n₄, hN''⟩ := hN' k hk
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = finestMesh L k := ⟨_, rfl⟩
  have heta : 0 < η := by
    rw [hη]
    exact zpow_pos hLpos _
  have hetaC : ((η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  obtain ⟨bz, hbz⟩ : ∃ bz, bz = S₂ * M₂ * (S₁ * M₁) * (S₂ * M₂) := ⟨_, rfl⟩
  obtain ⟨bn, hbn⟩ : ∃ bn, bn = S₄ * M₄ := ⟨_, rfl⟩
  obtain ⟨gb, hgb⟩ : ∃ gb, gb = S₃ * M₃ := ⟨_, rfl⟩
  obtain ⟨bq, hbq⟩ : ∃ bq, bq = η ^ 2 * gb + (η ^ 4)⁻¹ * (η ^ 2 * gb) := ⟨_, rfl⟩
  obtain ⟨bm, hbm⟩ : ∃ bm, bm = a * gb + 1 := ⟨_, rfl⟩
  have hbz0 : 0 ≤ bz := by rw [hbz]; positivity
  have hbn0 : 0 ≤ bn := by rw [hbn]; positivity
  have hgb0 : 0 ≤ gb := by rw [hgb]; positivity
  have hbq0 : 0 ≤ bq := by rw [hbq]; positivity
  have hbm0 : 0 ≤ bm := by rw [hbm]; positivity
  have hK0 : 0 ≤ saddleConstant a η bz bq bn bm := by
    unfold saddleConstant
    positivity
  refine ⟨saddleConstant a η bz bq bn bm + 1, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max n₁ n₂) (max (max n₃ n₄) 1))] with n hn
  have hn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₃ : n₃ ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hn
  have hn₄ : n₄ ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hn
  have hn0 : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) hn)
  obtain ⟨hB⟩ : Nonempty (∀ j, Fintype (PositiveEdge L n k j)) := ⟨fun j => by
    have : Finite (Edge L n k j) := PeriodicLattice.instFiniteBond _
    have : Finite (PositiveEdge L n k j) := Subtype.finite
    exact Fintype.ofFinite _⟩
  obtain ⟨w₁, hw₁⟩ : ∃ w, w = (inferInstance : Fintype (Fin 3 × PositiveEdge L n k 0 ⊕
        (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)))) := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w, w = (inferInstance : Fintype (Fin 3 × PositiveEdge L n k k)) := ⟨_, rfl⟩
  intro i₁ d₁ i₂ d₂ i₃ d₃ i₄ i₅ P
  classical
  obtain rfl : i₁ = w₁ := Subsingleton.elim _ _
  obtain rfl : i₂ = w₂ := Subsingleton.elim _ _
  subst hw₁ hw₂
  haveI : Finite (Face L n k 0) := finite_face 0
  haveI : Fintype (Fin 3 × Face L n k 0) := Fintype.ofFinite _
  obtain ⟨hXu, hXl, -⟩ := hF'' n hn₁ hn0
  obtain ⟨-, -, hru, -, hrl, -⟩ := hR'' n hn₂ hn0
  have hAl := hA'' n hn₃ hn0 0
  have hql := hAl.1.value_local
  have hGl := hAl.2.2.2.2.value_local
  obtain ⟨hNu, hNl⟩ := hN'' n hn₄ hn0
  obtain ⟨hQ, -, -⟩ := hNC a ha L hL k n hk hn0
  have nW : ‖(xiConjugated L n k 0 0 0)⁻¹‖ ≤ S₁ * M₁ := hb₁ L n k _ _ _ _ _ _ hL hn0 hM₁.le hXl
  have nr : ‖periodicEdgeResolventSqrt L n k‖ ≤ S₂ * M₂ := hb₂ L n k _ _ _ _ _ _ hL hn0 hM₂.le hrl
  have nq : ‖rescaledQAlong L n k 0 0 0‖ ≤ gb := by
    rw [hgb]
    exact hb₃ L n k _ _ _ _ _ _ hL hn0 hM₃.le hql
  have nG : ‖noiseAlong a L n k 0 0 0‖ ≤ gb := by
    rw [hgb]
    exact hb₃ L n k _ _ _ _ _ _ hL hn0 hM₃.le hGl
  have nNi : ‖(noiseBlockMatrix a (trivialField L n k 0))⁻¹‖ ≤ bn := by
    rw [hbn]
    exact hb₄ L n k _ _ _ _ _ _ hL hn0 hM₄.le hNl
  obtain ⟨p, hp⟩ : ∃ p, p = rescaledOperators L n k (trivialField L n k 0) := ⟨_, rfl⟩
  have hptop : p.coarse = 1 := by
    rw [hp]
    change (L : ℝ) ^ ((k : ℤ) - (k : ℤ)) = 1
    simp
  have hpη : p.eta = η := by
    rw [hp, hη]
    rfl
  have eq0 : rescaledQAlong L n k 0 0 0 = unitNormScale L k • Matrix.of p.Q := by
    rw [rescaledQAlong, twoSourceBackground_zero, hp]
  have eG : noiseAlong a L n k 0 0 0 =
      Matrix.of (noiseCovariance a L n k (trivialField L n k 0) k) := by
    rw [noiseAlong, twoSourceBackground_zero]
  have eX : xiConjugated L n k 0 0 0 =
      periodicEdgeResolventSqrt L n k * Matrix.of p.Xi * periodicEdgeResolventSqrt L n k := by
    rw [xiConjugated, twoSourceBackground_zero, hp]
  obtain ⟨r, hr⟩ : ∃ r, r = periodicEdgeResolventSqrt L n k := ⟨_, rfl⟩
  rw [← hr] at nr eX hru
  obtain ⟨Xi, hXi⟩ : ∃ Xi, Xi = Matrix.of p.Xi := ⟨_, rfl⟩
  rw [← hXi] at eX
  obtain ⟨W, hW⟩ : ∃ W, W = (xiConjugated L n k 0 0 0)⁻¹ := ⟨_, rfl⟩
  rw [← hW] at nW
  have hXiU : IsUnit (Matrix.det Xi) := by
    have h := hXu
    rw [eX, Matrix.det_mul, Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)
  have hWS : W * (r * Xi * r) = 1 := by
    rw [hW, ← eX]
    exact Matrix.nonsing_inv_mul _ hXu
  have hZeq : Xi⁻¹ = r * W * r := Matrix.inv_eq_left_inv (by
    have h2 : (W * r * Xi) * r = 1 := by simpa only [Matrix.mul_assoc] using hWS
    have h3 : r * (W * r * Xi) = 1 := mul_eq_one_comm.1 h2
    simpa only [Matrix.mul_assoc] using h3)
  obtain ⟨Z, hZd⟩ : ∃ Z, Z = Xi⁻¹ := ⟨_, rfl⟩
  have hZ1 : Z * Xi = 1 := by
    rw [hZd]
    exact Matrix.nonsing_inv_mul _ hXiU
  have nZ : ‖Z‖ ≤ bz := by
    rw [hZd, hZeq, hbz]
    calc ‖r * W * r‖ ≤ ‖r * W‖ * ‖r‖ := norm_mul_le _ _
      _ ≤ ‖r‖ * ‖W‖ * ‖r‖ := by
          gcongr
          exact norm_mul_le _ _
      _ ≤ _ := by gcongr
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = Matrix.of p.Q := ⟨_, rfl⟩
  obtain ⟨Qt, hQtd⟩ : ∃ Qt, Qt = Matrix.of p.Qt := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, G = Matrix.of (noiseCovariance a L n k (trivialField L n k 0) k) :=
    ⟨_, rfl⟩
  have hNeq : noiseBlockMatrix a (trivialField L n k 0) =
      Matrix.fromBlocks (-G - Q * Z * Qt) (-(Q * Z * Qt)) (-(Q * Z * Qt)) (1 - Q * Z * Qt) := by
    rw [noiseBlockMatrix, meanQTranspose, hQ, topCovariance, xiInv, hGd, hZd, hXi, hQd, hQtd, hp]
    rfl
  have hNi : (noiseBlockMatrix a (trivialField L n k 0))⁻¹ *
      Matrix.fromBlocks (-G - Q * Z * Qt) (-(Q * Z * Qt)) (-(Q * Z * Qt)) (1 - Q * Z * Qt) = 1 := by
    rw [← hNeq]
    exact Matrix.nonsing_inv_mul _ hNu
  have hone : (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n k 0 :=
    ⟨fun _ _ => one_mem _, fun _ _ => by simp⟩
  have hblk := Filter.Eventually.self_of_nhdsWithin
    (blocks_near_identity h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ ha hL hk hn0) hone
  obtain ⟨Mn, hΓ, hop⟩ := hblk
  obtain ⟨hop₁, hop₂⟩ := hop P
  have r1 : ∀ κ : Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1),
      (meanRadius (meanIterate (fun _ => (1 : ComplexMatrix2)) κ.1) κ.2.2.1).re = 1 := by
    intro κ
    have e2 : meanIterate (fun _ : Edge L n k 0 => (1 : ComplexMatrix2)) (κ.1 : ℕ) =
        fun _ => (1 : ComplexMatrix2) :=
      meanIterate_one hD hL hn0 κ.1 κ.1.2.le
    rw [e2, meanRadius_one hD hL hn0 κ.1.2 κ.2.2.2]
    simp
  simp only [r1, mul_one] at hΓ hop₁
  rw [← hη] at hop₁ hop₂
  have hG : G = ((a⁻¹ : ℝ) : ℂ) • (Mn * Mn.transpose) := by
    rw [hGd]
    refine hΓ.trans ?_
    have e : Matrix.diagonal (fun _ : (Σ i : Fin k, Fin 3 × PositiveEdge L n k (i + 1)) =>
        ((a : ℝ) : ℂ)⁻¹) = ((a⁻¹ : ℝ) : ℂ) • 1 := by
      rw [Complex.ofReal_inv, Matrix.smul_one_eq_diagonal]
    rw [e, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hQpk : Matrix.of (meanKernelQ L n k fun _ => (1 : ComplexMatrix2)) = Q := by
    have h := hQ
    rw [← hp] at h
    rw [hQd, ← h]
  rw [hQpk, ← Complex.ofReal_inv] at hop₂
  have hre : ∀ t κ, (Matrix.fromCols (((η⁻¹ : ℝ) : ℂ) • Q) Mn t κ).im = 0 := by
    intro t κ
    rw [← hop₂]
    simp [complexMatrixOfLinearMap]
  have hQre : ∀ t ι, (Q t ι).im = 0 := by
    intro t ι
    have h1 := hre t (.inl ι)
    rw [Matrix.fromCols_apply_inl, Matrix.smul_apply, smul_eq_mul, Complex.im_ofReal_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (inv_ne_zero heta.ne')
  have hMre : ∀ t κ, (Mn t κ).im = 0 := fun t κ => by
    have h1 := hre t (.inr κ)
    rwa [Matrix.fromCols_apply_inr] at h1
  have hMT := transpose_eq_conjTranspose_of_real Mn hMre
  have nG' : ‖G‖ ≤ gb := by
    rw [hGd, ← eG]
    exact nG
  have nMn : ‖Mn‖ ≤ bm := by
    have h1 := Matrix.l2_opNorm_conjTranspose_mul_self Mn.conjTranspose
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose, ← hMT] at h1
    have hac : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have h2 : Mn * Mn.transpose = ((a : ℝ) : ℂ) • G := by
      rw [hG, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hac, one_smul]
    have h3 : ‖Mn * Mn.transpose‖ ≤ a * gb := by
      rw [h2]
      refine (norm_smul_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
      gcongr
    rw [hbm]
    nlinarith [norm_nonneg Mn, sq_nonneg (‖Mn‖ - 1)]
  have nMt : ‖Mn.transpose‖ ≤ bm := by
    rw [hMT, Matrix.l2_opNorm_conjTranspose]
    exact nMn
  have nQ : ‖Q‖ ≤ η ^ 2 * gb := by
    have e : Q = ((η ^ 2 : ℝ) : ℂ) • (unitNormScale L k • Q) := by
      rw [smul_smul, unitNormScale, ← hη]
      have e1 : ((η ^ 2 : ℝ) : ℂ) * (((η ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
        push_cast
        field_simp
      rw [e1, one_smul]
    rw [e]
    refine (norm_smul_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), hQd, ← eq0]
    gcongr
  have eQt : Qt = (((η ^ 4)⁻¹ : ℝ) : ℂ) • Q.transpose := by
    ext ι t
    have e : Matrix.of p.Qt ι t = (((p.coarse ^ 4 / p.eta ^ 4 : ℝ)) : ℂ) * p.Q t ι := rfl
    rw [hQtd, e, hptop, hpη, hQd]
    simp
  have nQt : ‖Qt‖ ≤ (η ^ 4)⁻¹ * (η ^ 2 * gb) := by
    rw [eQt]
    refine (norm_smul_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      transpose_eq_conjTranspose_of_real Q hQre, Matrix.l2_opNorm_conjTranspose]
    gcongr
  have hQt : (((η⁻¹ : ℝ) : ℂ) • Q).transpose = ((η ^ 3 : ℝ) : ℂ) • Qt := by
    rw [eQt, Matrix.transpose_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  have hX : Matrix.of p.X = Xi - Qt * Q := by
    rw [hXi, hQtd, hQd, ← of_compKernel]
    rfl
  have hXb : (fun ι ι' => ((η ^ 2 : ℝ) : ℂ) * (rescaledOperators L n k fun _ => 1).X ι ι') =
      ((η ^ 2 : ℝ) : ℂ) • (Xi - Qt * Q) := by
    rw [← hX, hp]
    rfl
  rw [hXb] at hop₁
  have hS : saddlePointMatrix P a 0 = Matrix.fromBlocks
      (Matrix.fromBlocks (((η ^ 2 : ℝ) : ℂ) • (Xi - Qt * Q)) 0 0 ((a : ℂ) • 1))
      (Matrix.fromCols (((η⁻¹ : ℝ) : ℂ) • Q) Mn).transpose
      (Matrix.fromCols (((η⁻¹ : ℝ) : ℂ) • Q) Mn) 0 := by
    have em : expMove (0 : LevelTriple L n k).1 (unitPoint L n k) =
        quietPoint (trivialField L n k 0) := expMove_zero L n k
    rw [Matrix.smul_one_eq_diagonal, ← hop₁, ← hop₂]
    simp only [saddlePointMatrix, gaugeConstraintMatrix]
    rw [em]
    rfl
  have h2 := inv_bound_of_lower (saddlePointMatrix P a 0) hK0 fun v => by
    rw [hS]
    exact vnorm_le_saddleConstant_mul Xi Z hZ1 Q Qt G _ hNi Mn ha heta hG hQt nZ
      (hbq ▸ nQ.trans (le_add_of_nonneg_right (by positivity)))
      (hbq ▸ nQt.trans (le_add_of_nonneg_left (by positivity))) nNi nMn nMt v
  exact ⟨h2.1, h2.2.trans (by linarith)⟩
end YangMills.Construction.RunningCouplingSlope
end
