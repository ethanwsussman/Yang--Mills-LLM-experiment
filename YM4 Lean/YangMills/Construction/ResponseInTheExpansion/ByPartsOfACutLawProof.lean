import YangMills.Construction.ClusterExpansionOfAStep.SecondMomentOfAConvexLawProof
import YangMills.Construction.ResponseInTheExpansion.ByPartsOfACutLaw
import YangMills.Construction.SummableBoundsOfTheFlow.RadialSlopeOfACutProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open MeasureTheory ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem contDiff_radialCutoff_norm {ρ : ℝ} {r : ℝ → ℝ} (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) :
    ContDiff ℝ 1 fun v : BondVector => r ‖v‖ := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.contDiff_radialCutoff_norm <;> assumption
theorem hasFDerivAt_norm_bondVector {e : BondVector} (he : e ≠ 0) :
    HasFDerivAt (fun x : BondVector => ‖x‖) (‖e‖⁻¹ • innerSL ℝ e) e := by apply _root_.YangMills.SharedProofs.p11430 <;> assumption
theorem fderiv_cutoffFactor_norm {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (e v : BondVector)
    (he : ‖e‖ < ρ) :
    fderiv ℝ (fun x : BondVector => cutoffFactor ρ p (max ‖x‖ 0)) e v =
      -(cutoffFactor ρ p (max ‖e‖ 0) * cutoffRadialDeriv p e v) := by
  by_cases hzero : e = 0
  · subst hzero
    have hev : (fun x : BondVector => cutoffFactor ρ p (max ‖x‖ 0)) =ᶠ[nhds 0] fun _ => (1 : ℝ) := by
      have hball : Metric.ball (0 : BondVector) (5 * ρ / 8) ∈ nhds (0 : BondVector) :=
        Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [hball] with w hw
      have hw' : ‖w‖ < 5 * ρ / 8 := by simpa using hw
      have hmax : max ‖w‖ 0 = ‖w‖ := max_eq_left (norm_nonneg _)
      have hlt : ‖w‖ < ρ := by linarith
      simp only [hmax, cutoffFactor, if_pos hlt]
      rw [hp.vanish_small _ (norm_nonneg _) hw'.le]
      simp
    rw [hev.fderiv_eq]
    simp [cutoffRadialDeriv]
  · have hpos : 0 < ‖e‖ := norm_pos_iff.2 hzero
    have hmem : Set.Ico (0 : ℝ) ρ ∈ nhds ‖e‖ := Ico_mem_nhds hpos he
    have hpd : DifferentiableAt ℝ p ‖e‖ :=
      ((hp.smooth.contDiffAt hmem).differentiableAt (by simp))
    have hnear : (fun s : ℝ => cutoffFactor ρ p (max s 0)) =ᶠ[nhds ‖e‖] fun s => Real.exp (-p s) := by
      filter_upwards [Ioo_mem_nhds hpos he] with s hs
      simp only [max_eq_left hs.1.le, cutoffFactor, if_pos hs.2]
    have hd : HasDerivAt (fun s : ℝ => cutoffFactor ρ p (max s 0))
        (Real.exp (-p ‖e‖) * -deriv p ‖e‖) ‖e‖ :=
      (hpd.hasDerivAt.neg.exp).congr_of_eventuallyEq hnear
    have hcomp := hd.comp_hasFDerivAt e (hasFDerivAt_norm_bondVector hzero)
    have hsplit : (fun x : BondVector => cutoffFactor ρ p (max ‖x‖ 0)) =
        (fun s : ℝ => cutoffFactor ρ p (max s 0)) ∘ fun x : BondVector => ‖x‖ := rfl
    rw [hsplit, hcomp.fderiv]
    have hval : cutoffFactor ρ p (max ‖e‖ 0) = Real.exp (-p ‖e‖) := by
      simp only [max_eq_left hpos.le, cutoffFactor, if_pos he]
    rw [hval]
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, cutoffRadialDeriv]
    field_simp
theorem cutoffIntegrationByParts (hcut : CutoffFactorIsRadialCutoff) :
    cutoffIntegrationByPartsStatement := by
  intro ι _ _ ρ p Ψ g u hρ hp hΨ hg
  set r : ℝ → ℝ := fun t => cutoffFactor ρ p (max t 0) with hrdef
  have hr : IsRadialCutoff ρ r := hcut ρ p hρ hp
  have hnn : ∀ t, 0 ≤ t → 0 ≤ r t := by
    intro t ht
    rcases lt_or_ge t ρ with h | h
    · exact (hr.pos t ht h).le
    · rw [hr.zero t h]
  have hD : ballDensity (cutoffFactor ρ p) Ψ = ballDensity r Ψ := by
    funext η
    unfold ballDensity radialWeightProd
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [hrdef, max_eq_left (norm_nonneg (η b))]
  rw [hD]
  set φ : BondVector → ℝ := fun v => r ‖v‖ with hφ
  have hφs : ContDiff ℝ 1 φ := contDiff_radialCutoff_norm hρ hr
  have hφd : Differentiable ℝ φ := hφs.differentiable (by norm_num)
  have hRs : ContDiff ℝ 1 (radialWeightProd (ι := ι) r) := by
    unfold radialWeightProd
    apply contDiff_prod
    intro b _
    exact hφs.comp (contDiff_apply ℝ BondVector b)
  have hDs : ContDiff ℝ 1 (ballDensity r Ψ) := by
    unfold ballDensity
    exact hRs.mul hΨ.neg.exp
  have hDd : Differentiable ℝ (ballDensity r Ψ) := hDs.differentiable (by norm_num)
  have hDc : HasCompactSupport (ballDensity r Ψ) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) ρ) fun η hη => ?_
    by_contra hne
    apply hη
    have hR : radialWeightProd r η ≠ 0 := fun h => hne (by simp [ballDensity, h])
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hρ.le).mpr fun b => ?_
    by_contra hc
    push Not at hc
    exact hR (Finset.prod_eq_zero (Finset.mem_univ b) (hr.zero _ hc.le))
  have hDn : ∀ η, 0 ≤ ballDensity r Ψ η := fun η =>
    mul_nonneg (Finset.prod_nonneg fun b _ => hnn _ (norm_nonneg _)) (Real.exp_pos _).le
  have hgrad : ∀ η, fderiv ℝ (ballDensity r Ψ) η u =
      -(ballDensity r Ψ η * (fderiv ℝ Ψ η u + ∑ b, cutoffRadialDeriv p (η b) (u b))) := by
    intro η
    by_cases hb : ∀ b, ‖η b‖ < ρ
    · have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ η) η :=
        ((hΨ.differentiable (by norm_num)) η).hasFDerivAt
      have hprod : HasFDerivAt (fun ζ : BondField ι => ∏ b ∈ Finset.univ, φ (ζ b))
          (∑ b ∈ Finset.univ, (∏ j ∈ Finset.univ.erase b, φ (η j)) •
            ((fderiv ℝ φ (η b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b))) η := by
        apply HasFDerivAt.finsetProd
        intro b _
        exact ((hφd (η b)).hasFDerivAt).comp η
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
      have hR1 : (∑ b ∈ Finset.univ, (∏ j ∈ Finset.univ.erase b, φ (η j)) •
            ((fderiv ℝ φ (η b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b))) u =
          -(radialWeightProd r η * ∑ b, cutoffRadialDeriv p (η b) (u b)) := by
        rw [ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul]
        have h1 : fderiv ℝ φ (η b) (u b) = -(φ (η b) * cutoffRadialDeriv p (η b) (u b)) :=
          fderiv_cutoffFactor_norm hρ hp (η b) (u b) (hb b)
        rw [h1]
        have h2 : radialWeightProd r η = φ (η b) * ∏ j ∈ Finset.univ.erase b, φ (η j) :=
          (Finset.mul_prod_erase Finset.univ (fun j => φ (η j)) (Finset.mem_univ b)).symm
        rw [h2]
        ring
      have hE : HasFDerivAt (fun ζ => Real.exp (-Ψ ζ)) (Real.exp (-Ψ η) • (-fderiv ℝ Ψ η)) η :=
        hΨd.neg.exp
      have hfull := hprod.mul hE
      have e0 : fderiv ℝ (ballDensity r Ψ) η = _ := hfull.fderiv
      rw [e0]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.neg_apply]
      rw [hR1]
      have hpr : (∏ b ∈ Finset.univ, φ (η b)) = radialWeightProd r η := rfl
      rw [hpr]
      unfold ballDensity
      ring
    · have h0 : ballDensity r Ψ η = 0 := by
        push Not at hb
        obtain ⟨b, hb⟩ := hb
        unfold ballDensity radialWeightProd
        rw [Finset.prod_eq_zero (Finset.mem_univ b) (hr.zero _ hb)]
        simp
      have hmin : IsLocalMin (ballDensity r Ψ) η :=
        Filter.Eventually.of_forall fun ζ => by
          rw [h0]
          exact hDn ζ
      rw [hmin.fderiv_eq_zero, h0]
      simp
  have hgc : Continuous g := hg.continuous
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hFg : Continuous fun η => fderiv ℝ g η u :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hFD : Continuous fun η => fderiv ℝ (ballDensity r Ψ) η u :=
    (hDs.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have i1 : Integrable fun η => fderiv ℝ g η u * ballDensity r Ψ η :=
    Continuous.integrable_of_hasCompactSupport (hFg.mul hDs.continuous) hDc.mul_left
  have i2 : Integrable fun η => g η * fderiv ℝ (ballDensity r Ψ) η u :=
    Continuous.integrable_of_hasCompactSupport (hgc.mul hFD)
      (hDc.fderiv_apply (𝕜 := ℝ) u).mul_left
  have i3 : Integrable fun η => g η * ballDensity r Ψ η :=
    Continuous.integrable_of_hasCompactSupport (hgc.mul hDs.continuous) hDc.mul_left
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3 (fun x _ => hgd x)
    (fun x _ => hDd x)
  have e1 : ∫ η, g η * fderiv ℝ (ballDensity r Ψ) η u =
      -∫ η, g η * (fderiv ℝ Ψ η u + ∑ b, cutoffRadialDeriv p (η b) (u b)) * ballDensity r Ψ η := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    change g η * fderiv ℝ (ballDensity r Ψ) η u = _
    rw [hgrad]
    ring
  rw [e1] at key
  exact (neg_injective key).symm
end YangMills.Construction.WeightedResponses
end
