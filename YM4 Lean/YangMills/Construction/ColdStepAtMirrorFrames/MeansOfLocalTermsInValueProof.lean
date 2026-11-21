import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenInValueProofForm
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfLocalTermsInValue
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsTheExponentOfTheStepProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open MeasureTheory Metric
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace BallExtension
section Extension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℝ}
theorem openPolyball_eq_ball (hr : 0 < r) : openPolyball ι r = Metric.ball (0 : BondField ι) r := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.openPolyball_eq_ball <;> assumption
theorem isOpen_openPolyball (hr : 0 < r) : IsOpen (openPolyball ι r) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.isOpen_openPolyball <;> assumption
theorem exists_contDiff_eq_on_openPolyball (hr : 0 < r) {g : BondField ι → ℝ}
    (hg : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ r) → ContDiffAt ℝ 3 g η) :
    ∃ g' : BondField ι → ℝ, ContDiff ℝ 3 g' ∧ ∀ η ∈ openPolyball ι r, g' η = g η := by
  set U : Set (BondField ι) := {η | ContDiffAt ℝ 3 g η} with hU
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro η hη
    exact (ContDiffAt.eventually hη (by simp))
  have hK : closedBall (0 : BondField ι) r ⊆ U := fun η hη => by
    rw [mem_closedBall_zero_iff] at hη
    exact hg η fun b => (norm_le_pi_norm η b).trans hη
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall (0 : BondField ι) r).exists_cthickening_subset_open
    hUo hK
  rw [cthickening_closedBall hδ.le hr.le] at hsub
  let f : ContDiffBump (0 : BondField ι) := ⟨r + δ / 3, r + 2 * δ / 3, by positivity, by linarith⟩
  refine ⟨fun η => f η * g η, ?_, fun η hη => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : ‖y‖ ≤ r + δ
    · have : y ∈ U := hsub (by rw [mem_closedBall_zero_iff]; linarith)
      exact (f.contDiff.contDiffAt).mul this
    · have hy' : r + δ < ‖y‖ := not_le.mp hy
      have : (fun η => f η * g η) =ᶠ[nhds y] fun _ => (0 : ℝ) := by
        have hb : ball y (δ / 3) ∈ nhds y := ball_mem_nhds _ (by positivity)
        filter_upwards [hb] with z hz
        have h1 : ‖y‖ - ‖z‖ ≤ ‖y - z‖ := norm_sub_norm_le y z
        have h2 : ‖y - z‖ < δ / 3 := by
          rw [← dist_eq_norm, dist_comm]
          exact hz
        have h3 : r + 2 * δ / 3 ≤ dist z 0 := by
          rw [dist_zero_right]
          linarith
        rw [f.zero_of_le_dist h3, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq this
  · have hmem : η ∈ closedBall (0 : BondField ι) f.rIn := by
      rw [openPolyball_eq_ball hr] at hη
      rw [mem_closedBall_zero_iff]
      have h1 : ‖η‖ < r := by simpa using hη
      change ‖η‖ ≤ r + δ / 3
      linarith
    change f η * g η = g η
    rw [f.one_of_mem_closedBall hmem, one_mul]
theorem eventuallyEq_of_eqOn_openPolyball {f g : BondField ι → ℝ} (hr : 0 < r)
    (h : ∀ η ∈ openPolyball ι r, f η = g η)
    {η : BondField ι} (hη : η ∈ openPolyball ι r) : f =ᶠ[nhds η] g := by
  filter_upwards [(isOpen_openPolyball hr).mem_nhds hη] with ζ hζ using h ζ hζ
theorem bondGradNorm_congr {f g : BondField ι → ℝ} (hr : 0 < r)
    (h : ∀ η ∈ openPolyball ι r, f η = g η) {η : BondField ι} (hη : η ∈ openPolyball ι r) (b : ι) :
    bondGradNorm f b η = bondGradNorm g b η := by
  unfold bondGradNorm
  rw [(eventuallyEq_of_eqOn_openPolyball hr h hη).fderiv_eq]
theorem secondDerivAlong_congr {f g : BondField ι → ℝ} (hr : 0 < r)
    (h : ∀ η ∈ openPolyball ι r, f η = g η) {η : BondField ι} (hη : η ∈ openPolyball ι r)
    (u v : BondField ι) : secondDerivAlong f η u v = secondDerivAlong g η u v := by
  unfold secondDerivAlong
  have : (fun ζ => fderiv ℝ f ζ u) =ᶠ[nhds η] fun ζ => fderiv ℝ g ζ u := by
    filter_upwards [(isOpen_openPolyball hr).mem_nhds hη] with ζ hζ
    rw [(eventuallyEq_of_eqOn_openPolyball hr h hζ).fderiv_eq]
  rw [this.fderiv_eq]
theorem secondDerivAlong_smul_smul {f : BondField ι → ℝ} (hf : ContDiff ℝ 3 f) (η u v : BondField ι)
    (a c : ℝ) : secondDerivAlong f η (a • u) (c • v) = a * c * secondDerivAlong f η u v := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hd : Differentiable ℝ (fun ζ => fderiv ℝ f ζ u) :=
    (h1.differentiable (by simp)).clm_apply (differentiable_const u)
  unfold secondDerivAlong
  have e1 : (fun ζ => fderiv ℝ f ζ (a • u)) = fun ζ => a * fderiv ℝ f ζ u := by
    funext ζ
    simp
  rw [e1]
  have h2 : HasFDerivAt (fun ζ => a * fderiv ℝ f ζ u) (a • fderiv ℝ (fun ζ => fderiv ℝ f ζ u) η) η :=
    (hd η).hasFDerivAt.const_mul a
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
  ring
theorem bondVariation_smul (b : ι) (a : ℝ) (u : BondVector) :
    bondVariation b (a • u) = a • bondVariation b u := by apply _root_.YangMills.SharedProofs.p169 <;> assumption
theorem abs_secondDerivAlong_le_of_unit {f : BondField ι → ℝ} (hf : ContDiff ℝ 3 f) {η : BondField ι}
    {b b' : ι} {B : ℝ}
    (h : ∀ u u' : BondVector, ‖u‖ = 1 → ‖u'‖ = 1 →
      |secondDerivAlong f η (bondVariation b u) (bondVariation b' u')| ≤ B)
    (u u' : BondVector) :
    |secondDerivAlong f η (bondVariation b u) (bondVariation b' u')| ≤ B * ‖u‖ * ‖u'‖ := by
  by_cases hu : u = 0
  · subst hu
    have : bondVariation b (0 : BondVector) = 0 := by simp [bondVariation]
    rw [this]
    simp [secondDerivAlong]
  by_cases hu' : u' = 0
  · subst hu'
    have : bondVariation b' (0 : BondVector) = 0 := by simp [bondVariation]
    rw [this]
    simp [secondDerivAlong]
  have n1 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have n2 : ‖u'‖ ≠ 0 := norm_ne_zero_iff.mpr hu'
  have e1 : bondVariation b u = ‖u‖ • bondVariation b (‖u‖⁻¹ • u) := by
    rw [← bondVariation_smul, smul_smul, mul_inv_cancel₀ n1, one_smul]
  have e2 : bondVariation b' u' = ‖u'‖ • bondVariation b' (‖u'‖⁻¹ • u') := by
    rw [← bondVariation_smul, smul_smul, mul_inv_cancel₀ n2, one_smul]
  have h3 := h (‖u‖⁻¹ • u) (‖u'‖⁻¹ • u') (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n1])
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n2])
  have h4 : secondDerivAlong f η (bondVariation b u) (bondVariation b' u') =
      ‖u‖ * ‖u'‖ * secondDerivAlong f η (bondVariation b (‖u‖⁻¹ • u)) (bondVariation b' (‖u'‖⁻¹ • u')) := by
    rw [e1, e2, secondDerivAlong_smul_smul hf]
  rw [h4, abs_mul, abs_of_nonneg (by positivity)]
  calc _ ≤ ‖u‖ * ‖u'‖ * B := by gcongr
    _ = _ := by ring
end Extension
section ZeroExtension
variable {Λ ι : Type} [Fintype Λ] [DecidableEq Λ] [Fintype ι] [DecidableEq ι] {e : Λ → ι}
theorem zeroExtensionL_mem_openPolyball {r : ℝ} (hr : 0 < r) (he : Function.Injective e)
    {ζ : BondField Λ} (h : ζ ∈ openPolyball Λ r) : zeroExtensionL e ζ ∈ openPolyball ι r := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.zeroExtension_mem_polyball <;> assumption
end ZeroExtension
section Decomposition
variable {ι 𝒞 : Type} [Fintype ι] [DecidableEq ι] [Fintype 𝒞] [DecidableEq 𝒞] {r x κ A : ℝ}
  {pl : ι → 𝒞} {D : 𝒞 → 𝒞 → ℝ} {θ θ₁ : 𝒞 → BondField ι → ℝ} {Ψ Ψ₁ H H₁ : BondField ι → ℝ} {Y : 𝒞}
theorem isLocalDecomposition_of_extensions (hr : 0 < r)
    (hs : IsLocalDecompositionOnBalls r x κ A pl D θ Ψ H Y)
    (hθ : ∀ Z, ContDiff ℝ 3 (θ₁ Z)) (hθe : ∀ Z, ∀ η ∈ openPolyball ι r, θ₁ Z η = θ Z η)
    (hH : ContDiff ℝ 3 H₁) (hHe : ∀ η ∈ openPolyball ι r, H₁ η = H η)
    (hΨe : ∀ η ∈ openPolyball ι r, Ψ₁ η = Ψ η) : IsLocalDecomposition r x κ A pl D θ₁ Ψ₁ H₁ Y where
  smooth Z := (hθ Z).of_le (by norm_num)
  smooth_obs := hH.of_le (by norm_num)
  sum η hη := by
    rw [hΨe η hη, hs.sum η hη]
    exact Finset.sum_congr rfl fun Z _ => (hθe Z η hη).symm
  slope Z η hη b := by
    rw [bondGradNorm_congr hr (hθe Z) hη]
    exact hs.slope Z η hη b
  second Z η hη b b' u u' := by
    refine abs_secondDerivAlong_le_of_unit (hθ Z) (fun v v' hv hv' => ?_) u u'
    rw [secondDerivAlong_congr hr (hθe Z) hη]
    exact hs.second Z η hη b b' v v' hv hv'
  slope_obs η hη b := by
    rw [bondGradNorm_congr hr hHe hη]
    exact hs.slope_obs η hη b
end Decomposition
end BallExtension
open BallExtension in
theorem localExpectationComparisonInValue_holds (h₁ : ExpectationsAgreeInValue)
    (h₂ : CutoffExpectationIsPositiveForm) : LocalExpectationComparisonInValue := by
  intro S lam hl
  obtain ⟨C, hC₁, hC₂⟩ := h₁ S lam hl
  refine ⟨C, ?_, ?_⟩
  · intro ι 𝒞 _ _ _ _ ρ x κ A p pl D Ψ H Y hρ hp hκ hx hA hP hΨ hH hb
    obtain ⟨Ψ₁, K, hΨe, hK, hsl⟩ := hΨ
    obtain ⟨H₁, hH₁, hHe⟩ := exists_contDiff_eq_on_openPolyball hρ hH
    have hΨc : Continuous Ψ₁ := hK.smooth.continuous
    have hF := h₂ ι ρ p Ψ₁ hρ hp hΨc
    have e1 : ballExpectation (cutoffFactor ρ p) Ψ H = ballExpectation (cutoffFactor ρ p) Ψ₁ H₁ := by
      rw [hF.congr_on H₁ H hHe]
      exact (hF.congr_potential Ψ H fun η hη => hΨe η hη).symm
    rw [e1]
    refine hC₁ ι 𝒞 ρ x κ A p pl D Ψ₁ H₁ Y hρ hp hκ hx hA hP ⟨⟨K, hK⟩, hsl⟩ hH₁.continuous
      fun η hη => ?_
    rw [hHe η hη]
    exact hb η hη
  · intro ι ι' 𝒞 𝒞' Λ 𝒩 _ _ _ _ _ _ _ _ _ _ _ _ ρ x κ A ε rad p pl D pl' D' e e' n n' θ θ' Ψ H Ψ' H' Y Y'
      hρ hp hκ hx hA hε hrad hP hP' he he' hn hn' hD hDY hoff hoff' hfar hfar' hΨ hΨ' hs hs' hc
    obtain ⟨Ψ₁, K, hΨe, hK, hsl⟩ := hΨ
    obtain ⟨Ψ₁', K', hΨe', hK', hsl'⟩ := hΨ'
    choose θ₁ hθ₁ hθe using fun Z => exists_contDiff_eq_on_openPolyball hρ (hs.smooth Z)
    choose θ₁' hθ₁' hθe' using fun Z => exists_contDiff_eq_on_openPolyball hρ (hs'.smooth Z)
    obtain ⟨H₁, hH₁, hHe⟩ := exists_contDiff_eq_on_openPolyball hρ hs.smooth_obs
    obtain ⟨H₁', hH₁', hHe'⟩ := exists_contDiff_eq_on_openPolyball hρ hs'.smooth_obs
    have hF := h₂ ι ρ p Ψ₁ hρ hp hK.smooth.continuous
    have hF' := h₂ ι' ρ p Ψ₁' hρ hp hK'.smooth.continuous
    have e1 : ballExpectation (cutoffFactor ρ p) Ψ H = ballExpectation (cutoffFactor ρ p) Ψ₁ H₁ := by
      rw [hF.congr_on H₁ H hHe]
      exact (hF.congr_potential Ψ H fun η hη => hΨe η hη).symm
    have e2 : ballExpectation (cutoffFactor ρ p) Ψ' H' = ballExpectation (cutoffFactor ρ p) Ψ₁' H₁' := by
      rw [hF'.congr_on H₁' H' hHe']
      exact (hF'.congr_potential Ψ' H' fun η hη => hΨe' η hη).symm
    rw [e1, e2]
    have hcmp : IsCloseInValue ρ x κ ε pl D e e' n n' θ₁ θ₁' H₁ H₁' Y := by
      refine ⟨fun j ζ hζ => ?_, fun ζ hζ => ?_⟩
      · rw [hθe _ _ (zeroExtensionL_mem_openPolyball hρ he hζ),
          hθe' _ _ (zeroExtensionL_mem_openPolyball hρ he' hζ)]
        exact hc.terms j ζ hζ
      · rw [hHe _ (zeroExtensionL_mem_openPolyball hρ he hζ),
          hHe' _ (zeroExtensionL_mem_openPolyball hρ he' hζ)]
        exact hc.value ζ hζ
    exact hC₂ ι ι' 𝒞 𝒞' Λ 𝒩 ρ x κ A ε rad p pl D pl' D' e e' n n' θ₁ θ₁' Ψ₁ H₁ Ψ₁' H₁' Y Y'
      hρ hp hκ hx hA hε hrad hP hP' he he' hn hn' hD hDY hoff hoff' hfar hfar'
      ⟨⟨K, hK⟩, hsl⟩ ⟨⟨K', hK'⟩, hsl'⟩
      (isLocalDecomposition_of_extensions hρ hs hθ₁ hθe hH₁ hHe hΨe)
      (isLocalDecomposition_of_extensions hρ hs' hθ₁' hθe' hH₁' hHe' hΨe')
      hcmp
end YangMills.Construction.ColdStepAtMirrorFrames
end
