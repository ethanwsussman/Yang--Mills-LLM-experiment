import Mathlib
set_option autoImplicit false
noncomputable section
open Metric
namespace YangMills.Construction
namespace Analytic
def cauchyHalvingConstant : ℕ → ℝ
  | 0 => 1
  | k + 1 => 2 ^ (k + 1) * cauchyHalvingConstant k
theorem cauchyHalvingConstant_pos (k : ℕ) : 0 < cauchyHalvingConstant k := by
  induction k with
  | zero => simp [cauchyHalvingConstant]
  | succ k ih =>
    simp only [cauchyHalvingConstant]
    positivity
section Complex
variable {X E : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem norm_fderiv_apply_le_of_norm_le_on_ball {g : X → E} {ρ M : ℝ} (hg : AnalyticOnNhd ℂ g (ball 0 ρ))
    (hM : ∀ x ∈ ball (0 : X) ρ, ‖g x‖ ≤ M) {y : X} {r : ℝ} (hr : 0 < r) (hy : ‖y‖ + r < ρ) (v : X) :
    ‖fderiv ℂ g y v‖ ≤ M / r * ‖v‖ := by
  by_cases hv : v = 0
  · have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (by
      rw [mem_ball_zero_iff]
      linarith))
    simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set R : ℝ := r / ‖v‖ with hR
  have hRpos : 0 < R := div_pos hr hvn
  let h : ℂ → E := fun w => g (y + w • v)
  have hin : ∀ w ∈ closedBall (0 : ℂ) R, y + w • v ∈ ball (0 : X) ρ := by
    intro w hw
    have hw' : ‖w‖ ≤ R := by simpa using hw
    rw [mem_ball_zero_iff]
    calc ‖y + w • v‖ ≤ ‖y‖ + ‖w‖ * ‖v‖ := (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ ‖y‖ + R * ‖v‖ := by gcongr
      _ = ‖y‖ + r := by rw [hR, div_mul_cancel₀ _ hvn.ne']
      _ < ρ := hy
  have hline : ∀ w : ℂ, HasDerivAt (fun w : ℂ => y + w • v) v w := by
    intro w
    simpa using ((hasDerivAt_id w).smul_const v).const_add y
  have hdiff : ∀ w ∈ closedBall (0 : ℂ) R, HasDerivAt h (fderiv ℂ g (y + w • v) v) w := by
    intro w hw
    have h1 : HasFDerivAt g (fderiv ℂ g (y + w • v)) (y + w • v) :=
      (hg _ (hin w hw)).differentiableAt.hasFDerivAt
    exact h1.comp_hasDerivAt w (hline w)
  have hd : DiffContOnCl ℂ h (ball 0 R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hRpos.ne']
    exact fun w hw => (hdiff w hw).differentiableAt.differentiableWithinAt
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hd (C := M) fun w hw =>
    hM _ (hin w (sphere_subset_closedBall hw))
  rw [(hdiff 0 (by simp [hRpos.le])).deriv] at hb
  simp only [zero_smul, add_zero] at hb
  refine hb.trans (le_of_eq ?_)
  rw [hR]
  field_simp
theorem norm_iteratedFDeriv_zero_apply_le_of_norm_le_on_ball [CompleteSpace E] (k : ℕ) :
    ∀ {g : X → E} {ρ M : ℝ}, 0 < ρ →
    AnalyticOnNhd ℂ g (ball 0 ρ) → (∀ x ∈ ball (0 : X) ρ, ‖g x‖ ≤ M) → ∀ v : Fin k → X,
    ‖iteratedFDeriv ℂ k g 0 v‖ ≤ cauchyHalvingConstant k * M / ρ ^ k * ∏ l, ‖v l‖ := by
  induction k with
  | zero =>
    intro g ρ M hρ hg hM v
    simpa [cauchyHalvingConstant] using hM 0 (by simpa using hρ)
  | succ k ih =>
    intro g ρ M hρ hg hM v
    set w := v (Fin.last k) with hw
    let ap : (X →L[ℂ] E) →L[ℂ] E := ContinuousLinearMap.apply ℂ E w
    let g₁ : X → E := ap ∘ fderiv ℂ g
    have hfd : AnalyticOnNhd ℂ (fderiv ℂ g) (ball 0 ρ) := hg.fderiv
    have hsub : ball (0 : X) (ρ / 2) ⊆ ball 0 ρ := ball_subset_ball (by linarith)
    have hg₁ : AnalyticOnNhd ℂ g₁ (ball 0 (ρ / 2)) := fun y hy =>
      ap.analyticAt _ |>.comp (hfd y (hsub hy))
    have hb : ∀ y ∈ ball (0 : X) (ρ / 2), ‖g₁ y‖ ≤ M / (ρ / 2) * ‖w‖ := fun y hy => by
      have hy' : ‖y‖ < ρ / 2 := by simpa using hy
      exact norm_fderiv_apply_le_of_norm_le_on_ball hg hM (half_pos hρ) (by linarith) w
    have h1 := ih (half_pos hρ) hg₁ hb (Fin.init v)
    have h0 : (0 : X) ∈ ball (0 : X) ρ := by simpa using hρ
    have hcd : ContDiffAt ℂ k (fderiv ℂ g) 0 := (hfd 0 h0).contDiffAt
    have h2 : iteratedFDeriv ℂ (k + 1) g 0 v = iteratedFDeriv ℂ k g₁ 0 (Fin.init v) := by
      rw [iteratedFDeriv_succ_apply_right]
      have h3 := ap.iteratedFDeriv_comp_left hcd le_rfl
      rw [show g₁ = ap ∘ fderiv ℂ g from rfl, h3]
      rfl
    rw [h2]
    refine h1.trans (le_of_eq ?_)
    rw [Fin.prod_univ_castSucc]
    simp only [cauchyHalvingConstant, Fin.init]
    rw [div_pow, ← hw]
    have hρ' : ρ ≠ 0 := hρ.ne'
    field_simp
    ring
end Complex
section Real
variable {ι : Type} [Fintype ι] {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [CompleteSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
def complexifyCLM : (ι → ℝ) →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi fun l => Complex.ofRealCLM.comp (ContinuousLinearMap.proj l)
theorem complexifyCLM_apply (t : ι → ℝ) (l : ι) : complexifyCLM t l = (t l : ℂ) := rfl
theorem norm_complexifyCLM (t : ι → ℝ) : ‖complexifyCLM t‖ = ‖t‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l => ?_)
  · rw [complexifyCLM_apply, Complex.norm_real]
    exact norm_le_pi_norm t l
  · have := norm_le_pi_norm (complexifyCLM t) l
    rwa [complexifyCLM_apply, Complex.norm_real] at this
structure IsBoundedHolomorphicExtension (J : E' →L[ℝ] E) (f : (ι → ℝ) → E') (g : (ι → ℂ) → E) (ρ M : ℝ) :
    Prop where
  radius_pos : 0 < ρ
  analyticOnNhd : AnalyticOnNhd ℂ g (ball 0 ρ)
  norm_le : ∀ x ∈ ball (0 : ι → ℂ) ρ, ‖g x‖ ≤ M
  agrees_real : ∀ t : ι → ℝ, ‖t‖ < ρ → J (f t) = g (complexifyCLM t)
variable {J : E' →L[ℝ] E} {f : (ι → ℝ) → E'} {g : (ι → ℂ) → E} {ρ M : ℝ}
theorem IsBoundedHolomorphicExtension.eventuallyEq_comp (h : IsBoundedHolomorphicExtension J f g ρ M) :
    (J ∘ f) =ᶠ[nhds 0] g ∘ complexifyCLM := by
  have : ball (0 : ι → ℝ) ρ ∈ nhds (0 : ι → ℝ) := ball_mem_nhds _ h.radius_pos
  filter_upwards [this] with t ht
  exact h.agrees_real t (by simpa using ht)
theorem IsBoundedHolomorphicExtension.analyticAt_comp_complexify
    (h : IsBoundedHolomorphicExtension J f g ρ M) :
    AnalyticAt ℝ (g ∘ complexifyCLM) 0 := by
  have h0 : complexifyCLM (0 : ι → ℝ) ∈ ball (0 : ι → ℂ) ρ := by
    rw [map_zero]
    simpa using h.radius_pos
  have h1 : AnalyticAt ℝ g (complexifyCLM (0 : ι → ℝ)) :=
    (h.analyticOnNhd _ h0).restrictScalars
  exact h1.comp ((complexifyCLM (ι := ι)).analyticAt 0)
theorem IsBoundedHolomorphicExtension.analyticAt_of_leftInverse (h : IsBoundedHolomorphicExtension J f g ρ M)
    (P : E →L[ℝ] E') (hP : ∀ a, P (J a) = a) : AnalyticAt ℝ f 0 := by
  have h1 : AnalyticAt ℝ (P ∘ (g ∘ complexifyCLM)) 0 := (P.analyticAt _).comp h.analyticAt_comp_complexify
  refine h1.congr ?_
  filter_upwards [h.eventuallyEq_comp] with t ht
  have : J (f t) = g (complexifyCLM t) := ht
  simp only [Function.comp_apply]
  rw [← this, hP]
theorem IsBoundedHolomorphicExtension.norm_iteratedFDeriv_basis_le {m : ℕ} {f : (Fin m → ℝ) → E'}
    {g : (Fin m → ℂ) → E}
    (h : IsBoundedHolomorphicExtension J f g ρ M) (P : E →L[ℝ] E') (hP : ∀ a, P (J a) = a)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) :
    ‖iteratedFDeriv ℝ m f 0 (fun l => Pi.single l 1)‖ ≤ cauchyHalvingConstant m * M / ρ ^ m := by
  have hf : ContDiffAt ℝ m f 0 := (h.analyticAt_of_leftInverse P hP).contDiffAt
  have h0 : (0 : Fin m → ℂ) ∈ ball (0 : Fin m → ℂ) ρ := by simpa using h.radius_pos
  have hgC : ContDiffAt ℂ m g 0 := (h.analyticOnNhd 0 h0).contDiffAt
  have e1 : J (iteratedFDeriv ℝ m f 0 (fun l => Pi.single l 1)) =
      iteratedFDeriv ℝ m (J ∘ f) 0 (fun l => Pi.single l 1) := by
    rw [J.iteratedFDeriv_comp_left hf le_rfl]
    rfl
  have e2 : iteratedFDeriv ℝ m (J ∘ f) 0 = iteratedFDeriv ℝ m (g ∘ complexifyCLM) 0 :=
    (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) h.eventuallyEq_comp m).self_of_nhds
  have hs : IsOpen (ball (0 : Fin m → ℂ) ρ) := isOpen_ball
  have hs' : IsOpen ((complexifyCLM (ι := Fin m)) ⁻¹' ball (0 : Fin m → ℂ) ρ) :=
    hs.preimage (complexifyCLM (ι := Fin m)).continuous
  have hcd : ContDiffOn ℝ m g (ball (0 : Fin m → ℂ) ρ) := fun x hx =>
    ((h.analyticOnNhd x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt
  have hmem : (0 : Fin m → ℝ) ∈ (complexifyCLM (ι := Fin m)) ⁻¹' ball (0 : Fin m → ℂ) ρ := by
    simpa using h0
  have e3 : iteratedFDeriv ℝ m (g ∘ complexifyCLM) 0 =
      (iteratedFDeriv ℝ m g 0).compContinuousLinearMap fun _ => complexifyCLM (ι := Fin m) := by
    have h3 := (complexifyCLM (ι := Fin m)).iteratedFDerivWithin_comp_right hcd hs.uniqueDiffOn
      hs'.uniqueDiffOn hmem (i := m) le_rfl
    rw [iteratedFDerivWithin_of_isOpen m hs' hmem, map_zero, iteratedFDerivWithin_of_isOpen m hs h0] at h3
    exact h3
  have e4 : iteratedFDeriv ℝ m g 0 =
      (iteratedFDeriv ℂ m g 0).restrictScalars ℝ :=
    (hgC.restrictScalars_iteratedFDeriv (𝕜 := ℝ)).symm
  have hb := norm_iteratedFDeriv_zero_apply_le_of_norm_le_on_ball m h.radius_pos h.analyticOnNhd h.norm_le
    (fun l => complexifyCLM (Pi.single l 1 : Fin m → ℝ))
  rw [← hJ, e1, e2, e3, e4]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.coe_restrictScalars]
  refine hb.trans (le_of_eq ?_)
  simp [norm_complexifyCLM, Pi.norm_single]
end Real
end Analytic
end YangMills.Construction
end
