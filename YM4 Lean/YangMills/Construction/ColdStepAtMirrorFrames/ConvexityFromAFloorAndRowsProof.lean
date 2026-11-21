import YangMills.Construction.ColdStepAtMirrorFrames.ConvexityFromAFloorAndRows
import Mathlib
set_option autoImplicit false
noncomputable section
open Metric Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity
set_option linter.unusedSectionVars false
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem mem_closedBall_zero_iff_forall_norm_le {ρ : ℝ} (hρ : 0 ≤ ρ) (η : BondField ι) :
    η ∈ closedBall (0 : BondField ι) ρ ↔ ∀ b, ‖η b‖ ≤ ρ := by
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ]
theorem mem_ball_zero_iff_forall_norm_lt {ρ : ℝ} (hρ : 0 < ρ) (η : BondField ι) :
    η ∈ ball (0 : BondField ι) ρ ↔ ∀ b, ‖η b‖ < ρ := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff hρ]
theorem exists_contDiff_eq_on_closedBall {ρ : ℝ} (hρ : 0 < ρ) {f : BondField ι → ℝ}
    (hf : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 f η) :
    ∃ g : BondField ι → ℝ, ContDiff ℝ 3 g ∧ ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → g η = f η := by
  classical
  set U : Set (BondField ι) := {η | ContDiffAt ℝ 3 f η} with hU
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro η hη
    exact (ContDiffAt.eventually hη (by simp))
  have hK : IsCompact (closedBall (0 : BondField ι) ρ) := isCompact_closedBall _ _
  have hKU : closedBall (0 : BondField ι) ρ ⊆ U := fun η hη =>
    hf η ((mem_closedBall_zero_iff_forall_norm_le hρ.le η).1 hη)
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hUo hKU
  let χ : ContDiffBump (0 : BondField ι) :=
    ⟨ρ, ρ + δ, hρ, by linarith⟩
  refine ⟨fun η => χ η * f η, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro η
    by_cases hη : η ∈ U
    · exact (χ.contDiff.contDiffAt).mul hη
    · have hns : η ∉ tsupport χ := by
        intro hs
        rw [χ.tsupport_eq] at hs
        apply hη
        apply hδU
        rw [cthickening_closedBall hδ.le hρ.le]
        have hr : χ.rOut = δ + ρ := by simp [χ, add_comm]
        rw [← hr]
        exact hs
      have hz : (fun ζ => χ ζ * f ζ) =ᶠ[𝓝 η] fun _ => 0 := by
        have := notMem_tsupport_iff_eventuallyEq.1 hns
        filter_upwards [this] with ζ hζ
        simp [hζ]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · intro η hη
    have : χ η = 1 := χ.one_of_mem_closedBall ((mem_closedBall_zero_iff_forall_norm_le hρ.le η).2 hη)
    simp [this]
theorem differentiableAt_fderiv_apply {f : BondField ι → ℝ} {η : BondField ι}
    (hf : ContDiffAt ℝ 3 f η) (u : BondField ι) :
    DifferentiableAt ℝ (fun ζ => fderiv ℝ f ζ u) η := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) η := hf.fderiv_right (by norm_num)
  exact (h2.differentiableAt (by norm_num)).clm_apply (differentiableAt_const u)
theorem secondDerivAlong_eq_fderiv_fderiv {f : BondField ι → ℝ} {η : BondField ι}
    (hf : ContDiffAt ℝ 3 f η) (u v : BondField ι) :
    secondDerivAlong f η u v = fderiv ℝ (fderiv ℝ f) η v u := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) η := hf.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) η := h2.differentiableAt (by norm_num)
  unfold secondDerivAlong
  have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const u η)).fderiv
  rw [this]
  simp
theorem secondDerivAlong_const_mul_add {A R Ψ : BondField ι → ℝ} {x : ℝ} {η : BondField ι}
    {s : Set (BondField ι)} (hs : IsOpen s) (hη : η ∈ s)
    (hA : ∀ ζ ∈ s, ContDiffAt ℝ 3 A ζ) (hR : ∀ ζ ∈ s, ContDiffAt ℝ 3 R ζ)
    (hΨ : ∀ ζ ∈ s, Ψ ζ = x * A ζ + R ζ) (u v : BondField ι) :
    secondDerivAlong Ψ η u v = x * secondDerivAlong A η u v + secondDerivAlong R η u v := by
  have hgrad : ∀ ζ ∈ s, fderiv ℝ Ψ ζ u = x * fderiv ℝ A ζ u + fderiv ℝ R ζ u := by
    intro ζ hζ
    have he : Ψ =ᶠ[𝓝 ζ] fun ξ => x * A ξ + R ξ := by
      filter_upwards [hs.mem_nhds hζ] with ξ hξ using hΨ ξ hξ
    have hAd : DifferentiableAt ℝ A ζ := (hA ζ hζ).differentiableAt (by norm_num)
    have hRd : DifferentiableAt ℝ R ζ := (hR ζ hζ).differentiableAt (by norm_num)
    rw [he.fderiv_eq]
    have h1 : HasFDerivAt (fun ξ => x * A ξ + R ξ) (x • fderiv ℝ A ζ + fderiv ℝ R ζ) ζ :=
      (hAd.hasFDerivAt.const_mul x).add hRd.hasFDerivAt
    rw [h1.fderiv]
    simp
  have he : (fun ζ => fderiv ℝ Ψ ζ u) =ᶠ[𝓝 η] fun ζ => x * fderiv ℝ A ζ u + fderiv ℝ R ζ u := by
    filter_upwards [hs.mem_nhds hη] with ζ hζ using hgrad ζ hζ
  unfold secondDerivAlong
  rw [he.fderiv_eq]
  have h1 := ((differentiableAt_fderiv_apply (hA η hη) u).hasFDerivAt.const_mul x).add
    (differentiableAt_fderiv_apply (hR η hη) u).hasFDerivAt
  have h2 : HasFDerivAt (fun ζ => x * fderiv ℝ A ζ u + fderiv ℝ R ζ u) _ η := h1
  rw [h2.fderiv]
  simp
theorem secondDerivAlong_self_eq_sum {f : BondField ι → ℝ} {η : BondField ι}
    (hf : ContDiffAt ℝ 3 f η) (u : BondField ι) :
    secondDerivAlong f η u u =
      ∑ b, ∑ b', secondDerivAlong f η (bondVariation b (u b)) (bondVariation b' (u b')) := by
  have hu : u = ∑ b, bondVariation b (u b) := by
    unfold bondVariation
    exact (Finset.univ_sum_single u).symm
  have hs : ∀ v w : BondField ι, secondDerivAlong f η v w = fderiv ℝ (fderiv ℝ f) η w v :=
    secondDerivAlong_eq_fderiv_fderiv hf
  calc secondDerivAlong f η u u = fderiv ℝ (fderiv ℝ f) η u u := hs u u
    _ = fderiv ℝ (fderiv ℝ f) η (∑ b', bondVariation b' (u b')) (∑ b, bondVariation b (u b)) := by
        rw [← hu]
    _ = ∑ b, ∑ b', secondDerivAlong f η (bondVariation b (u b)) (bondVariation b' (u b')) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_sum, ContinuousLinearMap.sum_apply]
        refine Finset.sum_congr rfl fun b' _ => ?_
        exact (hs _ _).symm
theorem schur_test {K : ι → ι → ℝ} {M : ℝ} (hs : ∀ b b', K b b' = K b' b) (hK : ∀ b b', 0 ≤ K b b')
    (hr : ∀ b, ∑ b', K b b' ≤ M) (g : ι → ℝ) :
    ∑ b, ∑ b', K b b' * g b * g b' ≤ M * ∑ b, g b ^ 2 := by
  have h1 : ∀ b b', K b b' * g b * g b' ≤ K b b' * g b ^ 2 / 2 + K b b' * g b' ^ 2 / 2 := by
    intro b b'
    nlinarith [hK b b', sq_nonneg (g b - g b'), mul_nonneg (hK b b') (sq_nonneg (g b - g b'))]
  have h2 : ∑ b, ∑ b', K b b' * g b' ^ 2 / 2 = ∑ b, ∑ b', K b b' * g b ^ 2 / 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [hs b' b]
  have h3 : ∀ b, ∑ b', K b b' * g b ^ 2 / 2 ≤ M * g b ^ 2 / 2 := by
    intro b
    have : ∑ b', K b b' * g b ^ 2 / 2 = (∑ b', K b b') * g b ^ 2 / 2 := by
      rw [Finset.sum_mul, Finset.sum_div]
    rw [this]
    have := mul_le_mul_of_nonneg_right (hr b) (sq_nonneg (g b))
    linarith
  calc ∑ b, ∑ b', K b b' * g b * g b'
      ≤ ∑ b, ∑ b', (K b b' * g b ^ 2 / 2 + K b b' * g b' ^ 2 / 2) :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => h1 b b'
    _ = ∑ b, ∑ b', K b b' * g b ^ 2 / 2 + ∑ b, ∑ b', K b b' * g b' ^ 2 / 2 := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ b, ∑ b', K b b' * g b ^ 2 / 2 := by rw [h2]; ring
    _ ≤ 2 * ∑ b, M * g b ^ 2 / 2 := by
        have := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => h3 b
        linarith
    _ = M * ∑ b, g b ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
theorem convexityOfHessianFloorPlusSmallRows_holds : ConvexityOfHessianFloorPlusSmallRows := by
  intro ι _ _ ρ x lam κ d A R KA KR hρ hx hlam hκ hd hA hR hfloor hKA hKR hsA hsR hR0 hrA hrR
  obtain ⟨Ψ, hΨs, hΨ⟩ := exists_contDiff_eq_on_closedBall (f := fun η => x * A η + R η) hρ
    (fun η hη => (contDiffAt_const.mul (hA η hη)).add (hR η hη))
  set s : Set (BondField ι) := ball (0 : BondField ι) ρ with hs
  have hso : IsOpen s := isOpen_ball
  have hsm : ∀ η ∈ s, ∀ b, ‖η b‖ < ρ := fun η hη => (mem_ball_zero_iff_forall_norm_lt hρ η).1 hη
  have hAs : ∀ ζ ∈ s, ContDiffAt ℝ 3 A ζ := fun ζ hζ => hA ζ fun b => (hsm ζ hζ b).le
  have hRs : ∀ ζ ∈ s, ContDiffAt ℝ 3 R ζ := fun ζ hζ => hR ζ fun b => (hsm ζ hζ b).le
  have hΨb : ∀ ζ ∈ s, Ψ ζ = x * A ζ + R ζ := fun ζ hζ => hΨ ζ fun b => (hsm ζ hζ b).le
  have hsec : ∀ η, (∀ b, ‖η b‖ < ρ) → ∀ u v : BondField ι,
      secondDerivAlong Ψ η u v = x * secondDerivAlong A η u v + secondDerivAlong R η u v :=
    fun η hη u v =>
      secondDerivAlong_const_mul_add hso ((mem_ball_zero_iff_forall_norm_lt hρ η).2 hη) hAs hRs hΨb u v
  have hexp : ∀ b b', 1 ≤ Real.exp (2 * κ * d b b') := fun b b' =>
    Real.one_le_exp (by have := hd b b'; positivity)
  have hrow : ∀ b, ∑ b', KR b b' ≤ x * lam / 16 := by
    intro b
    refine le_trans (Finset.sum_le_sum fun b' _ => ?_) (hrR b)
    have := mul_le_mul_of_nonneg_left (hexp b b') (hR0 b b')
    linarith
  refine ⟨Ψ, fun η hη => hΨ η fun b => (hη b).le, ?_, ?_⟩
  · refine ⟨hΨs, ?_, ?_, ?_, ?_⟩
    · intro η hη u
      have hfl := hfloor η hη u
      have hηs : η ∈ s := (mem_ball_zero_iff_forall_norm_lt hρ η).2 hη
      have hQ : |secondDerivAlong R η u u| ≤ x * lam / 16 * ∑ b, ‖u b‖ ^ 2 := by
        rw [secondDerivAlong_self_eq_sum (hRs η hηs) u]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine le_trans (Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _) ?_
        refine le_trans (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ =>
          hKR η hη b b' (u b) (u b')) ?_
        exact schur_test hsR hR0 hrow fun b => ‖u b‖
      rw [hsec η hη]
      have h1 := (abs_le.1 hQ).1
      have h2 : x * (lam * ∑ b, ‖u b‖ ^ 2) ≤ x * secondDerivAlong A η u u :=
        mul_le_mul_of_nonneg_left hfl hx.le
      have h3 : 0 ≤ x * lam * ∑ b, ‖u b‖ ^ 2 := by positivity
      nlinarith
    · intro η hη b b' e e'
      rw [hsec η hη]
      have h1 := hKA η hη b b' e e'
      have h2 := hKR η hη b b' e e'
      calc |x * secondDerivAlong A η (bondVariation b e) (bondVariation b' e') +
            secondDerivAlong R η (bondVariation b e) (bondVariation b' e')|
          ≤ |x * secondDerivAlong A η (bondVariation b e) (bondVariation b' e')| +
              |secondDerivAlong R η (bondVariation b e) (bondVariation b' e')| := abs_add_le _ _
        _ = x * |secondDerivAlong A η (bondVariation b e) (bondVariation b' e')| +
              |secondDerivAlong R η (bondVariation b e) (bondVariation b' e')| := by
            rw [abs_mul, abs_of_pos hx]
        _ ≤ x * (KA b b' * ‖e‖ * ‖e'‖) + KR b b' * ‖e‖ * ‖e'‖ := by
            have := mul_le_mul_of_nonneg_left h1 hx.le
            linarith
        _ = (x * KA b b' + KR b b') * ‖e‖ * ‖e'‖ := by ring
    · intro b b'
      simp only [hsA b b', hsR b b']
    · intro b
      have h1 : ∑ b', (x * KA b b' + KR b b') * (Real.exp (2 * κ * d b b') - 1) =
          x * ∑ b', KA b b' * (Real.exp (2 * κ * d b b') - 1) +
            ∑ b', KR b b' * (Real.exp (2 * κ * d b b') - 1) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b' _ => ?_
        ring
      have h2 : ∑ b', KR b b' * (Real.exp (2 * κ * d b b') - 1) ≤ x * lam / 16 := by
        refine le_trans (Finset.sum_le_sum fun b' _ => ?_) (hrR b)
        have := hR0 b b'
        nlinarith
      have h3 := mul_le_mul_of_nonneg_left (hrA b) hx.le
      rw [h1]
      have h4 : 0 ≤ x * lam := by positivity
      nlinarith
  · intro b e
    have h0 : (0 : BondField ι) ∈ s := mem_ball_self hρ
    have he : Ψ =ᶠ[𝓝 (0 : BondField ι)] fun ξ => x * A ξ + R ξ := by
      filter_upwards [hso.mem_nhds h0] with ξ hξ using hΨb ξ hξ
    unfold bondPartialDeriv
    rw [he.fderiv_eq]
    have hAd : DifferentiableAt ℝ A 0 := (hAs 0 h0).differentiableAt (by norm_num)
    have hRd : DifferentiableAt ℝ R 0 := (hRs 0 h0).differentiableAt (by norm_num)
    have h1 : HasFDerivAt (fun ξ => x * A ξ + R ξ) (x • fderiv ℝ A 0 + fderiv ℝ R 0) 0 :=
      (hAd.hasFDerivAt.const_mul x).add hRd.hasFDerivAt
    rw [h1.fderiv]
    simp
end YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity
end
