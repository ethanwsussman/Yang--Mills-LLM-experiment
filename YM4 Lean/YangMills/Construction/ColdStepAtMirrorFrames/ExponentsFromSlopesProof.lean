import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeAlongRaysOfADifference
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ExponentDifferenceBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Finset ι) (ρ x B₀ A Mq Gq : ℝ) (g g' Q Q' : BondField ι → ℝ),
    0 < ρ → 0 ≤ x → ContDiffOn ℝ 2 g (openPolyball ι ρ) → ContDiffOn ℝ 2 g' (openPolyball ι ρ) →
    ContDiffOn ℝ 2 Q (openPolyball ι ρ) → ContDiffOn ℝ 2 Q' (openPolyball ι ρ) →
    (∀ k ∈ B, ∀ e, |bondPartialDeriv g' k 0 e - bondPartialDeriv g k 0 e| ≤ B₀ * ‖e‖) →
    (∀ ξ ∈ openPolyball ι ρ, ∀ k ∈ B, ∀ l e e',
      |secondDerivAlong g' ξ (bondVariation k e) (bondVariation l e') -
        secondDerivAlong g ξ (bondVariation k e) (bondVariation l e')| ≤ A * ‖e‖ * ‖e'‖) →
    (∀ ξ ∈ openPolyball ι ρ, |Q' ξ - Q ξ| ≤ Mq) →
    (∀ ξ ∈ openPolyball ι ρ, ∀ (k : ι) (e : BondVector), ‖e‖ = 1 →
      |bondPartialDeriv Q' k ξ e - bondPartialDeriv Q k ξ e| ≤ Gq) →
    ∀ ξ ∈ openPolyball ι ρ,
      |(x * radialSlopeIntegral B g' ξ - Q' ξ) - (x * radialSlopeIntegral B g ξ - Q ξ)| ≤
        x * ∑ k ∈ B, ‖ξ k‖ * (B₀ + A * ∑ l, ‖ξ l‖) + Mq ∧
      ∀ l, bondGradNorm (fun ζ => (x * radialSlopeIntegral B g' ζ - Q' ζ) - (x * radialSlopeIntegral B g ζ - Q ζ)) l ξ ≤
        x * ((if l ∈ B then B₀ + A * ∑ l', ‖ξ l'‖ else 0) + A * ∑ k ∈ B, ‖ξ k‖) + Gq
end YangMills.Construction.ColdStepAtMirrorFrames
end

noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem isOpen_openPolyball (ρ : ℝ) : IsOpen (openPolyball ι ρ) := by apply _root_.YangMills.DeltaSharedProofs.p3020 <;> assumption
omit [DecidableEq ι] in
theorem smul_mem_openPolyball {ρ t : ℝ} {ξ : BondField ι} (hξ : ξ ∈ openPolyball ι ρ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : t • ξ ∈ openPolyball ι ρ := fun b => by
  have h1 : ‖(t • ξ) b‖ = |t| * ‖ξ b‖ := by simp [norm_smul]
  have h2 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have h3 := hξ b
  rw [h1]
  nlinarith [norm_nonneg (ξ b), abs_nonneg t]
theorem bondPartialDeriv_sub {ρ : ℝ} {f f' : BondField ι → ℝ} (hf : ContDiffOn ℝ 2 f (openPolyball ι ρ))
    (hf' : ContDiffOn ℝ 2 f' (openPolyball ι ρ)) {ξ : BondField ι} (hξ : ξ ∈ openPolyball ι ρ) (k : ι)
    (e : BondVector) :
    bondPartialDeriv (fun ζ => f' ζ - f ζ) k ξ e = bondPartialDeriv f' k ξ e - bondPartialDeriv f k ξ e := by
  have ho := isOpen_openPolyball (ι := ι) ρ
  have d : DifferentiableAt ℝ f ξ := (hf.contDiffAt (ho.mem_nhds hξ)).differentiableAt (by norm_num)
  have d' : DifferentiableAt ℝ f' ξ := (hf'.contDiffAt (ho.mem_nhds hξ)).differentiableAt (by norm_num)
  unfold bondPartialDeriv
  rw [fderiv_fun_sub d' d]
  rfl
theorem secondDerivAlong_sub {ρ : ℝ} {f f' : BondField ι → ℝ} (hf : ContDiffOn ℝ 2 f (openPolyball ι ρ))
    (hf' : ContDiffOn ℝ 2 f' (openPolyball ι ρ)) {ξ : BondField ι} (hξ : ξ ∈ openPolyball ι ρ)
    (u v : BondField ι) :
    secondDerivAlong (fun ζ => f' ζ - f ζ) ξ u v = secondDerivAlong f' ξ u v - secondDerivAlong f ξ u v := by
  have ho := isOpen_openPolyball (ι := ι) ρ
  have hd : ∀ {g : BondField ι → ℝ}, ContDiffOn ℝ 2 g (openPolyball ι ρ) →
      DifferentiableAt ℝ (fun ζ => fderiv ℝ g ζ u) ξ := fun hg => by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ _) (openPolyball ι ρ) := hg.fderiv_of_isOpen ho (by norm_num)
    exact ((h1.contDiffAt (ho.mem_nhds hξ)).differentiableAt (by norm_num)).clm_apply (differentiableAt_const u)
  have hev : (fun ζ => fderiv ℝ (fun ζ => f' ζ - f ζ) ζ u) =ᶠ[nhds ξ]
      fun ζ => fderiv ℝ f' ζ u - fderiv ℝ f ζ u := by
    filter_upwards [ho.mem_nhds hξ] with ζ hζ
    have d : DifferentiableAt ℝ f ζ := (hf.contDiffAt (ho.mem_nhds hζ)).differentiableAt (by norm_num)
    have d' : DifferentiableAt ℝ f' ζ := (hf'.contDiffAt (ho.mem_nhds hζ)).differentiableAt (by norm_num)
    rw [fderiv_fun_sub d' d]
    rfl
  unfold secondDerivAlong
  rw [hev.fderiv_eq, fderiv_fun_sub (hd hf') (hd hf)]
  rfl
theorem radialSlopeIntegral_sub {ρ : ℝ} {f f' : BondField ι → ℝ} (B : Finset ι)
    (hf : ContDiffOn ℝ 2 f (openPolyball ι ρ)) (hf' : ContDiffOn ℝ 2 f' (openPolyball ι ρ))
    {ξ : BondField ι} (hξ : ξ ∈ openPolyball ι ρ) :
    radialSlopeIntegral B f' ξ - radialSlopeIntegral B f ξ = radialSlopeIntegral B (fun ζ => f' ζ - f ζ) ξ := by
  have ho := isOpen_openPolyball (ι := ι) ρ
  have hc : ∀ {g : BondField ι → ℝ}, ContDiffOn ℝ 2 g (openPolyball ι ρ) → ∀ k,
      IntervalIntegrable (fun t : ℝ => bondPartialDeriv g k (t • ξ) (ξ k)) MeasureTheory.volume 0 1 :=
      fun {g} hg k => by
    have h1 : ContinuousOn (fderiv ℝ g) (openPolyball ι ρ) :=
      (hg.fderiv_of_isOpen ho (m := 1) (by norm_num)).continuousOn
    have hm : Set.MapsTo (fun t : ℝ => t • ξ) (Set.Icc 0 1) (openPolyball ι ρ) :=
      fun t ht => smul_mem_openPolyball hξ ht
    have hcs : ContinuousOn (fun t : ℝ => t • ξ) (Set.Icc 0 1) :=
      (continuous_id.smul continuous_const).continuousOn
    have h2 : ContinuousOn (fun t : ℝ => bondPartialDeriv g k (t • ξ) (ξ k)) (Set.Icc 0 1) :=
      (h1.comp hcs hm).clm_apply continuousOn_const
    rw [← Set.uIcc_of_le zero_le_one] at h2
    exact h2.intervalIntegrable
  unfold radialSlopeIntegral
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← intervalIntegral.integral_sub (hc hf' k) (hc hf k)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact ht
  exact (bondPartialDeriv_sub hf hf' (smul_mem_openPolyball hξ ht') k (ξ k)).symm
theorem exponentDifferenceBound_of_radialSlopeIntegralBound (hR : RadialSlopeIntegralBound) :
    ExponentDifferenceBound := by
  intro ι _ _ B ρ x B₀ A Mq Gq f f' Q Q' hρ hx hf hf' hQ hQ' h0 h2 hq hgq ξ hξ
  have ho := isOpen_openPolyball (ι := ι) ρ
  have hD : ContDiffOn ℝ 2 (fun ζ => f' ζ - f ζ) (openPolyball ι ρ) := hf'.sub hf
  have z0 : (0 : BondField ι) ∈ openPolyball ι ρ := fun b => by simpa using hρ
  have hr := hR ι B ρ B₀ A (fun ζ => f' ζ - f ζ) hρ hD
    (fun k hk e => by
      rw [bondPartialDeriv_sub hf hf' z0]
      exact h0 k hk e)
    (fun ζ hζ k hk l e e' => by
      rw [secondDerivAlong_sub hf hf' hζ]
      exact h2 ζ hζ k hk l e e') ξ hξ
  obtain ⟨hdiff, hval, hgrad⟩ := hr
  have hev : (fun ζ => (x * radialSlopeIntegral B f' ζ - Q' ζ) - (x * radialSlopeIntegral B f ζ - Q ζ)) =ᶠ[nhds ξ]
      fun ζ => x * radialSlopeIntegral B (fun ζ => f' ζ - f ζ) ζ - (Q' ζ - Q ζ) := by
    filter_upwards [ho.mem_nhds hξ] with ζ hζ
    rw [← radialSlopeIntegral_sub B hf hf' hζ]
    ring
  constructor
  · have e := hev.self_of_nhds
    simp only at e
    rw [e]
    have h3 := hq ξ hξ
    refine (abs_sub _ _).trans (add_le_add ?_ h3)
    rw [abs_mul, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_left hval hx
  · intro l
    have hQd : DifferentiableAt ℝ (fun ζ => Q' ζ - Q ζ) ξ :=
      (hQ'.sub hQ |>.contDiffAt (ho.mem_nhds hξ)).differentiableAt (by norm_num)
    have hRd : DifferentiableAt ℝ (fun ζ => x * radialSlopeIntegral B (fun ζ => f' ζ - f ζ) ζ) ξ :=
      hdiff.const_mul x
    have hfd : fderiv ℝ (fun ζ => (x * radialSlopeIntegral B f' ζ - Q' ζ) - (x * radialSlopeIntegral B f ζ - Q ζ)) ξ =
        x • fderiv ℝ (radialSlopeIntegral B (fun ζ => f' ζ - f ζ)) ξ - fderiv ℝ (fun ζ => Q' ζ - Q ζ) ξ := by
      rw [hev.fderiv_eq, fderiv_fun_sub hRd hQd, fderiv_const_mul hdiff]
    unfold bondGradNorm
    rw [hfd]
    have hGq : 0 ≤ Gq := by
      have := hgq ξ hξ l (EuclideanSpace.single 0 1) (by simp)
      exact (abs_nonneg _).trans this
    have hnorm : ‖(fderiv ℝ (fun ζ => Q' ζ - Q ζ) ξ).comp
        (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) l)‖ ≤ Gq := by
      refine ContinuousLinearMap.opNorm_le_bound _ hGq fun e => ?_
      by_cases he : e = 0
      · simp [he]
      have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
      have hu : ‖‖e‖⁻¹ • e‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm]
        field_simp
      have h3 := hgq ξ hξ l _ hu
      have h4 := bondPartialDeriv_sub hQ hQ' hξ l (‖e‖⁻¹ • e)
      rw [← h4] at h3
      have e2 : e = ‖e‖ • (‖e‖⁻¹ • e) := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      have h5 : ((fderiv ℝ (fun ζ => Q' ζ - Q ζ) ξ).comp
          (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) l)) e =
          ‖e‖ * bondPartialDeriv (fun ζ => Q' ζ - Q ζ) l ξ (‖e‖⁻¹ • e) := by
        conv_lhs => rw [e2]
        rw [map_smul, smul_eq_mul]
        rfl
      rw [h5, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg e), mul_comm]
      exact mul_le_mul_of_nonneg_right h3 (norm_nonneg e)
    have hsplit : (x • fderiv ℝ (radialSlopeIntegral B (fun ζ => f' ζ - f ζ)) ξ -
        fderiv ℝ (fun ζ => Q' ζ - Q ζ) ξ).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) l) =
        x • (fderiv ℝ (radialSlopeIntegral B (fun ζ => f' ζ - f ζ)) ξ).comp
          (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) l) -
        (fderiv ℝ (fun ζ => Q' ζ - Q ζ) ξ).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) l) := by
      ext e
      simp
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ?_ hnorm)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_left (hgrad l) hx
end YangMills.Construction.ColdStepAtMirrorFrames
end
