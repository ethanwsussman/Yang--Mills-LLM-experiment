import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativesOfABoundedExtension
import Mathlib
set_option autoImplicit false
noncomputable section
open Metric
namespace YangMills.Construction.Analytic
section Complex
variable {X E : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]
def cauchyEstimateBound (M ρ : ℝ) (k : ℕ) : ℝ := cauchyHalvingConstant k * M / (ρ / 2) ^ k
theorem cauchyEstimateBound_nonneg {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 < ρ) (k : ℕ) : 0 ≤ cauchyEstimateBound M ρ k := by
  have := cauchyHalvingConstant_pos k
  unfold cauchyEstimateBound
  positivity
theorem norm_iteratedFDeriv_apply_le_of_norm_le_halfBall (k : ℕ) {g : X → E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hg : AnalyticOnNhd ℂ g (ball 0 ρ))
    (hM : ∀ x ∈ ball (0 : X) ρ, ‖g x‖ ≤ M) {x : X} (hx : ‖x‖ ≤ ρ / 2) (v : Fin k → X) :
    ‖iteratedFDeriv ℂ k g x v‖ ≤ cauchyEstimateBound M ρ k * ∏ l, ‖v l‖ := by
  have hin : ∀ z ∈ ball (0 : X) (ρ / 2), z + x ∈ ball (0 : X) ρ := fun z hz => by
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖z + x‖ ≤ ‖z‖ + ‖x‖ := norm_add_le _ _
      _ < ρ := by linarith
  have h1 : AnalyticOnNhd ℂ (fun z => g (z + x)) (ball 0 (ρ / 2)) := fun z hz =>
    AnalyticAt.comp' (hg _ (hin z hz)) (analyticAt_id.add analyticAt_const)
  have h2 := norm_iteratedFDeriv_zero_apply_le_of_norm_le_on_ball k (half_pos hρ) h1
    (fun z hz => hM _ (hin z hz)) v
  rw [iteratedFDeriv_comp_add_right, zero_add] at h2
  exact h2
theorem norm_iteratedFDeriv_le_of_norm_le_halfBall (k : ℕ) {g : X → E} {ρ M : ℝ} (hρ : 0 < ρ) (hM0 : 0 ≤ M)
    (hg : AnalyticOnNhd ℂ g (ball 0 ρ)) (hM : ∀ x ∈ ball (0 : X) ρ, ‖g x‖ ≤ M) {x : X} (hx : ‖x‖ ≤ ρ / 2) :
    ‖iteratedFDeriv ℂ k g x‖ ≤ cauchyEstimateBound M ρ k :=
  ContinuousMultilinearMap.opNorm_le_bound (cauchyEstimateBound_nonneg hM0 hρ k)
    fun v => norm_iteratedFDeriv_apply_le_of_norm_le_halfBall k hρ hg hM hx v
theorem norm_iteratedFDeriv_apply_sub_zero_le (k : ℕ) {g : X → E} {ρ M : ℝ} (hρ : 0 < ρ) (hM0 : 0 ≤ M)
    (hg : AnalyticOnNhd ℂ g (ball 0 ρ)) (hM : ∀ x ∈ ball (0 : X) ρ, ‖g x‖ ≤ M) {x : X} (hx : ‖x‖ ≤ ρ / 2)
    (u : Fin k → X) :
    ‖iteratedFDeriv ℂ k g x u - iteratedFDeriv ℂ k g 0 u‖ ≤
      cauchyEstimateBound M ρ (k + 1) * (∏ l, ‖u l‖) * ‖x‖ := by
  set s := closedBall (0 : X) (ρ / 2) with hs
  have hsub : s ⊆ ball (0 : X) ρ := closedBall_subset_ball (by linarith)
  let ap : (ContinuousMultilinearMap ℂ (fun _ : Fin k => X) E) →L[ℂ] E :=
    ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => X) E u
  let φ : X → E := fun y => ap (iteratedFDeriv ℂ k g y)
  have hit : AnalyticOnNhd ℂ (iteratedFDeriv ℂ k g) (ball 0 ρ) := hg.iteratedFDeriv k
  have hd : ∀ y ∈ s, HasFDerivAt (iteratedFDeriv ℂ k g) (fderiv ℂ (iteratedFDeriv ℂ k g) y) y := fun y hy =>
    (hit y (hsub hy)).differentiableAt.hasFDerivAt
  have hφ : ∀ y ∈ s, HasFDerivAt φ (ap.comp (fderiv ℂ (iteratedFDeriv ℂ k g) y)) y := fun y hy =>
    ap.hasFDerivAt.comp y (hd y hy)
  set C := cauchyEstimateBound M ρ (k + 1) * ∏ l, ‖u l‖ with hC
  have hC0 : 0 ≤ C :=
    mul_nonneg (cauchyEstimateBound_nonneg hM0 hρ _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hb : ∀ y ∈ s, ‖fderiv ℂ φ y‖ ≤ C := fun y hy => by
    rw [(hφ y hy).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun d => ?_
    have h1 := norm_iteratedFDeriv_apply_le_of_norm_le_halfBall (k + 1) hρ hg hM (x := y)
      (by simpa [hs] using hy) (Fin.cons d u)
    rw [iteratedFDeriv_succ_apply_left, Fin.prod_univ_succ] at h1
    simp only [Fin.cons_zero, Fin.cons_succ] at h1
    have e : (Fin.tail (Fin.cons d u : Fin (k + 1) → X) : Fin k → X) = u := Fin.tail_cons _ _
    rw [e] at h1
    refine h1.trans (le_of_eq ?_)
    rw [hC]
    ring
  have h0 : (0 : X) ∈ s := by
    rw [hs]
    exact mem_closedBall_self (by linarith)
  have hxs : x ∈ s := by simpa [hs] using hx
  have h1 := (convex_closedBall (0 : X) (ρ / 2)).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℂ) (f := φ) (fun y hy => (hφ y hy).differentiableAt) hb h0 hxs
  rw [sub_zero] at h1
  exact h1
theorem norm_iteratedFDeriv_apply_sub_zero_apply_le (k : ℕ) {g : X → E} {ρ M : ℝ} (hρ : 0 < ρ) (hM0 : 0 ≤ M)
    (hg : AnalyticOnNhd ℂ g (ball 0 ρ)) (hM : ∀ x ∈ ball (0 : X) ρ, ‖g x‖ ≤ M) {x : X} (hx : ‖x‖ ≤ ρ / 2)
    (u v : Fin k → X) :
    ‖iteratedFDeriv ℂ k g x v - iteratedFDeriv ℂ k g 0 u‖ ≤
      cauchyEstimateBound M ρ (k + 1) * (∏ l, ‖u l‖) * ‖x‖ +
        cauchyEstimateBound M ρ k * ∑ l, ‖v l - u l‖ * ∏ l' ∈ Finset.univ.erase l, max ‖v l'‖ ‖u l'‖ := by
  have h1 := norm_iteratedFDeriv_apply_sub_zero_le k hρ hM0 hg hM hx u
  have h2 := (iteratedFDeriv ℂ k g x).norm_image_sub_le' v u
  have h3 : ∑ l, ∏ l', (if l' = l then ‖v l - u l‖ else max ‖v l'‖ ‖u l'‖) =
      ∑ l, ‖v l - u l‖ * ∏ l' ∈ Finset.univ.erase l, max ‖v l'‖ ‖u l'‖ := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]
    simp only [if_true]
    congr 1
    refine Finset.prod_congr rfl fun l' hl' => ?_
    rw [if_neg (Finset.ne_of_mem_erase hl')]
  rw [h3] at h2
  have h4 : ‖iteratedFDeriv ℂ k g x‖ ≤ cauchyEstimateBound M ρ k :=
    norm_iteratedFDeriv_le_of_norm_le_halfBall k hρ hM0 hg hM hx
  have h5 : 0 ≤ ∑ l, ‖v l - u l‖ * ∏ l' ∈ Finset.univ.erase l, max ‖v l'‖ ‖u l'‖ :=
    Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => by positivity)
  have e : iteratedFDeriv ℂ k g x v - iteratedFDeriv ℂ k g 0 u =
      (iteratedFDeriv ℂ k g x v - iteratedFDeriv ℂ k g x u) +
        (iteratedFDeriv ℂ k g x u - iteratedFDeriv ℂ k g 0 u) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h6 := h2.trans (mul_le_mul_of_nonneg_right h4 h5)
  linarith
theorem iteratedFDeriv_comp_affine_zero_apply {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {g : X → E} {ρ : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball 0 ρ)) {c₀ : X} (hc : ‖c₀‖ < ρ) (Lc : Y →L[ℂ] X) (k : ℕ) (v : Fin k → Y) :
    iteratedFDeriv ℂ k (fun T => g (c₀ + Lc T)) 0 v = iteratedFDeriv ℂ k g c₀ (fun l => Lc (v l)) := by
  set g₁ : X → E := fun z => g (z + c₀) with hg₁
  set s := ball (0 : X) (ρ - ‖c₀‖) with hs
  have hopen : IsOpen s := isOpen_ball
  have hopen' : IsOpen (Lc ⁻¹' s) := hopen.preimage Lc.continuous
  have hpos : 0 < ρ - ‖c₀‖ := by linarith
  have hin : ∀ z ∈ s, z + c₀ ∈ ball (0 : X) ρ := fun z hz => by
    rw [hs, mem_ball_zero_iff] at hz
    rw [mem_ball_zero_iff]
    calc ‖z + c₀‖ ≤ ‖z‖ + ‖c₀‖ := norm_add_le _ _
      _ < ρ := by linarith
  have hcd : ContDiffOn ℂ k g₁ s := fun z hz => by
    have h1 : AnalyticAt ℂ (fun z' => g (z' + c₀)) z :=
      AnalyticAt.comp' (hg _ (hin z hz)) (analyticAt_id.add analyticAt_const)
    exact h1.contDiffAt.contDiffWithinAt
  have h0 : (0 : X) ∈ s := by simpa [hs] using hpos
  have hmem : (0 : Y) ∈ Lc ⁻¹' s := by simpa using h0
  have h := Lc.iteratedFDerivWithin_comp_right hcd hopen.uniqueDiffOn hopen'.uniqueDiffOn hmem (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hopen' hmem, map_zero, iteratedFDerivWithin_of_isOpen k hopen h0] at h
  have e1 : (fun T => g (c₀ + Lc T)) = g₁ ∘ Lc := by
    funext T
    simp [hg₁, add_comm]
  rw [e1, h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hg₁, iteratedFDeriv_comp_add_right, zero_add]
end Complex
section Real
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [CompleteSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
theorem iteratedFDeriv_real_eq_complex_of_extension {m : ℕ} {f : (Fin m → ℝ) → E'} {G : (Fin m → ℂ) → E}
    (J : E' →L[ℝ] E) (P : E →L[ℝ] E')
    (hP : ∀ a, P (J a) = a) (hG : AnalyticAt ℂ G 0)
    (hf : ∀ᶠ t in nhds (0 : Fin m → ℝ), J (f t) = G (complexifyCLM t)) :
    J (iteratedFDeriv ℝ m f 0 (fun l => Pi.single l 1)) =
      iteratedFDeriv ℂ m G 0 (fun l => complexifyCLM (Pi.single l 1 : Fin m → ℝ)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hG.eventually_analyticAt
  have hs : IsOpen (ball (0 : Fin m → ℂ) ε) := isOpen_ball
  have hs' : IsOpen ((complexifyCLM (ι := Fin m)) ⁻¹' ball (0 : Fin m → ℂ) ε) :=
    hs.preimage (complexifyCLM (ι := Fin m)).continuous
  have h0 : (0 : Fin m → ℂ) ∈ ball (0 : Fin m → ℂ) ε := by simpa using hε
  have hmem : (0 : Fin m → ℝ) ∈ (complexifyCLM (ι := Fin m)) ⁻¹' ball (0 : Fin m → ℂ) ε := by simpa using h0
  have hcd : ContDiffOn ℝ m G (ball (0 : Fin m → ℂ) ε) := fun x hx =>
    ((hball x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt
  have hGc0 : AnalyticAt ℝ G (complexifyCLM (0 : Fin m → ℝ)) := by
    rw [map_zero]
    exact hG.restrictScalars
  have hGc : AnalyticAt ℝ (G ∘ complexifyCLM) 0 := hGc0.comp ((complexifyCLM (ι := Fin m)).analyticAt 0)
  have hfa : AnalyticAt ℝ f 0 := by
    have h1 : AnalyticAt ℝ (P ∘ (G ∘ complexifyCLM)) 0 := (P.analyticAt _).comp hGc
    refine h1.congr ?_
    filter_upwards [hf] with t ht
    simp only [Function.comp_apply]
    rw [← ht, hP]
  have e1 : J (iteratedFDeriv ℝ m f 0 (fun l => Pi.single l 1)) =
      iteratedFDeriv ℝ m (J ∘ f) 0 (fun l => Pi.single l 1) := by
    rw [J.iteratedFDeriv_comp_left hfa.contDiffAt le_rfl]
    rfl
  have hev : (J ∘ f) =ᶠ[nhds 0] G ∘ complexifyCLM := hf
  have e2 : iteratedFDeriv ℝ m (J ∘ f) 0 = iteratedFDeriv ℝ m (G ∘ complexifyCLM) 0 :=
    (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev m).self_of_nhds
  have e3 : iteratedFDeriv ℝ m (G ∘ complexifyCLM) 0 =
      (iteratedFDeriv ℝ m G 0).compContinuousLinearMap fun _ => complexifyCLM (ι := Fin m) := by
    have h3 := (complexifyCLM (ι := Fin m)).iteratedFDerivWithin_comp_right hcd hs.uniqueDiffOn
      hs'.uniqueDiffOn hmem (i := m) le_rfl
    rw [iteratedFDerivWithin_of_isOpen m hs' hmem, map_zero, iteratedFDerivWithin_of_isOpen m hs h0] at h3
    exact h3
  have e4 : iteratedFDeriv ℝ m G 0 = (iteratedFDeriv ℂ m G 0).restrictScalars ℝ :=
    ((hball 0 h0).contDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ)).symm
  rw [e1, e2, e3, e4]
  rfl
end Real
end YangMills.Construction.Analytic
end
