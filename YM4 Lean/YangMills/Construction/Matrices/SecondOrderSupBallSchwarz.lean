import YangMills.Construction.Matrices.SecondOrderSupBallBound
import YangMills.Construction.Matrices.TracelessHolomorphyDifferentiableHolds
import Mathlib
set_option autoImplicit false
open Set Metric Filter Asymptotics
open scoped Topology Matrix.Norms.L2Operator
open YangMills.Construction.Coordinates
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.SecondOrderSupBall
variable {σ : Type}
theorem supNorm_eq_norm [Fintype σ] [Nonempty σ] (A : σ → ComplexMatrix2) : supNorm A = ‖A‖ := by
  refine le_antisymm (ciSup_le fun i => norm_le_pi_norm A i) ?_
  refine (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg fun i => norm_nonneg _)).2 fun i => ?_
  exact le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (A i)) (Set.finite_range _).bddAbove i
theorem mem_tracelessPi_iff (A : σ → ComplexMatrix2) :
    A ∈ tracelessPi σ ↔ A ∈ tracelessPiSubmodule σ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.TracelessDifferentiable.mem_tracelessPi_iff_mem_submodule <;> assumption
def matrixEquivLinear : ComplexMatrix2 →ₗ[ℂ] ComplexCoordinates 4 where
  toFun := ComplexCoordinates.matrixEquiv
  map_add' X Y := by
    funext k
    simp [ComplexCoordinates.matrixEquiv]
  map_smul' c X := by
    funext k
    simp [ComplexCoordinates.matrixEquiv]
theorem norm_le_mul_div_sq_of_double_zero {g : ℂ → ComplexMatrix2} {υ M : ℝ}
    (hd : DifferentiableOn ℂ g (ball 0 υ)) (hM : ∀ z ∈ ball (0 : ℂ) υ, ‖g z‖ ≤ M)
    (h0 : g 0 = 0) (hg : HasDerivAt g 0 0) {z : ℂ} (hz : z ∈ ball (0 : ℂ) υ) :
    ‖g z‖ ≤ M * (‖z‖ / υ) ^ 2 := by
  have hmaps : MapsTo g (ball 0 υ) (closedBall (g 0) M) := fun w hw => by
    simpa [h0] using hM w hw
  have hsmall : (fun w => g w - g 0) =o[𝓝 0] fun w : ℂ => ‖w - 0‖ ^ 1 := by
    have hlittle := hasDerivAt_iff_isLittleO_nhds_zero.1 hg
    simpa using hlittle.norm_right
  have hschwarz := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hd hmaps hsmall hz
  simpa [h0, dist_eq_norm] using hschwarz
theorem secondOrderBoundOnSupBall_of_differentiable
    (h : HolomorphicOnTracelessIffDifferentiable) : SecondOrderBoundOnSupBall := by
  intro σ _ _ υ M hυ hM b N hN hbound hzero hline A hA
  have hlin : IsLinearMap ℂ (ComplexCoordinates.matrixEquiv : ComplexMatrix2 → ComplexCoordinates 4) :=
    matrixEquivLinear.isLinear
  have hdiff := ((h σ ComplexMatrix2 4 b ComplexCoordinates.matrixEquiv hlin (supBall σ υ) N).1 hN).2
  have hnonneg : 0 ≤ supNorm A := by
    rw [supNorm_eq_norm]
    exact norm_nonneg _
  rcases hnonneg.eq_or_lt with hnorm | hpos
  · have hA0 : A = 0 := norm_eq_zero.1 (by rw [← supNorm_eq_norm]; exact hnorm.symm)
    rw [← hnorm, hA0, hzero]
    simp
  · obtain ⟨a, ha⟩ : ∃ a, a = supNorm A := ⟨_, rfl⟩
    rw [← ha] at hpos ⊢
    have hlt : a < υ := ha ▸ hA.2
    have hane : (a : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hAmem : A ∈ tracelessPiSubmodule σ := (mem_tracelessPi_iff A).1 hA.1
    let B : ↥(tracelessPiSubmodule σ) := (a : ℂ)⁻¹ • ⟨A, hAmem⟩
    have hBnorm : ‖(B : σ → ComplexMatrix2)‖ = 1 := by
      have hB : (B : σ → ComplexMatrix2) = (a : ℂ)⁻¹ • A := rfl
      rw [hB, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le,
        ← supNorm_eq_norm, ← ha, inv_mul_cancel₀ hpos.ne']
    let g : ℂ → ComplexMatrix2 := fun z => N (z • (B : σ → ComplexMatrix2))
    have hmaps : MapsTo (fun z : ℂ => z • B) (ball 0 υ) (Subtype.val ⁻¹' supBall σ υ) := by
      intro z hz
      refine ⟨(mem_tracelessPi_iff _).2 (z • B).2, ?_⟩
      have hzB : ((z • B : ↥(tracelessPiSubmodule σ)) : σ → ComplexMatrix2) =
          z • (B : σ → ComplexMatrix2) := rfl
      rw [hzB, supNorm_eq_norm, norm_smul, hBnorm, mul_one]
      simpa using hz
    have hgd : DifferentiableOn ℂ g (ball 0 υ) :=
      hdiff.comp (differentiable_id.smul_const B).differentiableOn hmaps
    have hgM : ∀ z ∈ ball (0 : ℂ) υ, ‖g z‖ ≤ M := fun z hz => hbound _ (hmaps hz)
    have hg0 : g 0 = 0 := by
      simp [g, hzero]
    have hderiv : HasDerivAt g 0 0 := by
      have hat : DifferentiableAt ℂ g 0 :=
        hgd.differentiableAt (ball_mem_nhds _ hυ)
      have hL := (LinearMap.toContinuousLinearMap matrixEquivLinear).hasFDerivAt.comp_hasDerivAt
        (0 : ℂ) hat.hasDerivAt
      have hline' := hline (B : σ → ComplexMatrix2) ((mem_tracelessPi_iff _).2 B.2)
      have hval : matrixEquivLinear (deriv g 0) = 0 := hL.unique hline'
      have hderivZero : deriv g 0 = 0 := by
        apply ComplexCoordinates.matrixEquiv.injective
        have hmap0 : ComplexCoordinates.matrixEquiv (0 : ComplexMatrix2) = 0 :=
          map_zero matrixEquivLinear
        exact hval.trans hmap0.symm
      exact hderivZero ▸ hat.hasDerivAt
    have hamem : (a : ℂ) ∈ ball (0 : ℂ) υ := by
      simpa [abs_of_pos hpos] using hlt
    have hfin := norm_le_mul_div_sq_of_double_zero hgd hgM hg0 hderiv hamem
    have hgA : g (a : ℂ) = N A := by
      have hB : (B : σ → ComplexMatrix2) = (a : ℂ)⁻¹ • A := rfl
      simp only [g, hB, smul_smul, mul_inv_cancel₀ hane, one_smul]
    rw [hgA, Complex.norm_real, Real.norm_of_nonneg hpos.le] at hfin
    refine hfin.trans_eq ?_
    field_simp
end YangMills.Construction.Matrices.GroupLieProduct.SecondOrderSupBall
end
