import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreLocal
import YangMills.Construction.RunningCouplingSlope.MixedDerivativeByCellsProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.LocalityProof
open Tower
section OneVariable
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma norm_deriv_le_of_ball {g : ℂ → E} {w₀ : ℂ} {R C : ℝ} (hR : 0 < R)
    (hd : ∀ w, ‖w - w₀‖ < R → DifferentiableAt ℂ g w) (hb : ∀ w, ‖w - w₀‖ < R → ‖g w‖ ≤ C) :
    ‖deriv g w₀‖ ≤ 2 * C / R := by
  have h2 : 0 < R / 2 := by positivity
  have hh : ∀ z ∈ Metric.closedBall w₀ (R / 2), ‖z - w₀‖ < R := by
    intro z hz
    have : ‖z - w₀‖ ≤ R / 2 := by simpa [dist_eq_norm] using hz
    linarith
  have hdc : DiffContOnCl ℂ g (Metric.ball w₀ (R / 2)) :=
    DifferentiableOn.diffContOnCl_ball
      (fun z hz => (hd z (hh z hz)).differentiableWithinAt) subset_rfl
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le h2 hdc
    fun z hz => hb z (hh z (Metric.sphere_subset_closedBall hz))
  calc ‖deriv g w₀‖ ≤ C / (R / 2) := this
    _ = 2 * C / R := by field_simp
private lemma norm_sub_le_of_ball {g : ℂ → E} {R C : ℝ} (hR : 0 < R)
    (hd : ∀ w, ‖w‖ < R → DifferentiableAt ℂ g w) (hb : ∀ w, ‖w‖ < R → ‖g w‖ ≤ C) {σ : ℂ}
    (hσ : ‖σ‖ ≤ R / 2) : ‖g σ - g 0‖ ≤ 4 * C / R * ‖σ‖ := by
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) (R / 2)) := convex_closedBall _ _
  have hin : ∀ x ∈ Metric.closedBall (0 : ℂ) (R / 2), ‖x‖ ≤ R / 2 := by
    intro x hx
    simpa [dist_eq_norm] using hx
  have h1 : ∀ x ∈ Metric.closedBall (0 : ℂ) (R / 2), DifferentiableAt ℂ g x := fun x hx =>
    hd x (by have := hin x hx; linarith)
  have h2 : ∀ x ∈ Metric.closedBall (0 : ℂ) (R / 2), ‖deriv g x‖ ≤ 4 * C / R := by
    intro x hx
    have hx' := hin x hx
    have tri : ∀ w, ‖w - x‖ < R / 2 → ‖w‖ < R := by
      intro w hw
      have : ‖w‖ ≤ ‖w - x‖ + ‖x‖ := by simpa using norm_add_le (w - x) x
      linarith
    have := norm_deriv_le_of_ball (w₀ := x) (R := R / 2) (C := C) (by positivity)
      (fun w hw => hd w (tri w hw)) fun w hw => hb w (tri w hw)
    calc ‖deriv g x‖ ≤ 2 * C / (R / 2) := this
      _ = 4 * C / R := by field_simp; ring
  have := hs.norm_image_sub_le_of_norm_deriv_le h1 h2 (y := σ) (x := 0)
    (Metric.mem_closedBall_self (by positivity)) (by simpa [dist_eq_norm] using hσ)
  simpa using this
private lemma norm_deriv_sub_le {G : ℂ → ℂ → E} {R₁ R₂ C : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (h₁ : ∀ σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → DifferentiableAt ℂ (fun σ' => G σ' τ) σ)
    (h₂ : ∀ σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → DifferentiableAt ℂ (fun τ' => G σ τ') τ)
    (hb : ∀ σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → ‖G σ τ‖ ≤ C) {σ : ℂ} (hσ : ‖σ‖ ≤ R₁ / 2) :
    ‖deriv (fun τ => G σ τ) 0 - deriv (fun τ => G 0 τ) 0‖ ≤ 8 * C / (R₁ * R₂) * ‖σ‖ := by
  have hσ' : ‖σ‖ < R₁ := by linarith
  have h0 : ‖(0 : ℂ)‖ < R₁ := by simpa using hR₁
  have h0' : ‖(0 : ℂ)‖ < R₂ := by simpa using hR₂
  have e : deriv (fun τ => G σ τ) 0 - deriv (fun τ => G 0 τ) 0 =
      deriv (fun τ => G σ τ - G 0 τ) 0 :=
    (deriv_fun_sub (h₂ σ 0 hσ' h0') (h₂ 0 0 h0 h0')).symm
  rw [e]
  have hL : ∀ τ, ‖τ - 0‖ < R₂ → ‖G σ τ - G 0 τ‖ ≤ 4 * C / R₁ * ‖σ‖ := by
    intro τ hτ
    rw [sub_zero] at hτ
    exact norm_sub_le_of_ball hR₁ (fun w hw => h₁ w τ hw hτ) (fun w hw => hb w τ hw hτ) hσ
  have := norm_deriv_le_of_ball (w₀ := 0) hR₂ (fun w hw => by
    rw [sub_zero] at hw
    exact (h₂ σ w hσ' hw).sub (h₂ 0 w h0 hw)) hL
  calc _ ≤ 2 * (4 * C / R₁ * ‖σ‖) / R₂ := this
    _ = 8 * C / (R₁ * R₂) * ‖σ‖ := by field_simp; ring
end OneVariable
private abbrev IsC2At (F : ℝ → ℝ → ℂ) : Prop := ContDiffAt ℝ 2 (fun w : ℝ × ℝ => F w.1 w.2) 0
private lemma IsC2At.eventually_differentiableAt {F : ℝ → ℝ → ℂ} (h : IsC2At F) :
    ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun w : ℝ × ℝ => F w.1 w.2) (s, 0) := by
  have h1 : ∀ᶠ w in 𝓝 (0 : ℝ × ℝ), ContDiffAt ℝ 2 (fun w : ℝ × ℝ => F w.1 w.2) w :=
    ContDiffAt.eventually h (by simp)
  have h2 : Filter.Tendsto (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
    have : Continuous (fun s : ℝ => ((s, 0) : ℝ × ℝ)) := by fun_prop
    exact this.tendsto 0
  filter_upwards [h2.eventually h1] with s hs
  exact hs.differentiableAt (by norm_num)
private lemma IsC2At.differentiableAt_deriv {F : ℝ → ℝ → ℂ} (h : IsC2At F) :
    DifferentiableAt ℝ (fun s => deriv (fun t => F s t) 0) 0 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fun w : ℝ × ℝ => F w.1 w.2)) 0 :=
    ContDiffAt.fderiv_right h (by norm_num)
  have h3 : DifferentiableAt ℝ (fderiv ℝ (fun w : ℝ × ℝ => F w.1 w.2)) ((0 : ℝ), (0 : ℝ)) :=
    h1.differentiableAt (by norm_num)
  have h2 : DifferentiableAt ℝ (fun s : ℝ => ((s, 0) : ℝ × ℝ)) 0 := by fun_prop
  have h4 : DifferentiableAt ℝ
      (fun s : ℝ => fderiv ℝ (fun w : ℝ × ℝ => F w.1 w.2) (s, 0)) 0 :=
    DifferentiableAt.comp (f := fun s : ℝ => ((s, 0) : ℝ × ℝ)) (0 : ℝ) h3 h2
  have h5 : DifferentiableAt ℝ
      (fun s : ℝ => fderiv ℝ (fun w : ℝ × ℝ => F w.1 w.2) (s, 0) ((0 : ℝ), (1 : ℝ))) 0 :=
    h4.clm_apply (differentiableAt_const _)
  refine h5.congr_of_eventuallyEq ?_
  filter_upwards [IsC2At.eventually_differentiableAt h] with s hs
  have hp : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) s).prodMk (hasDerivAt_id (0 : ℝ))
  have := (hs.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hp)
  exact this.deriv
private lemma derivs_eq_zero_of_const_first {f : ℝ → ℝ → ℂ} {g : ℝ → ℂ}
    (h : ∀ᶠ w : ℝ × ℝ in 𝓝 (0, 0), f w.1 w.2 = g w.2) :
    deriv (fun s => f s 0) 0 = 0 ∧ deriv (fun s => deriv (fun t => f s t) 0) 0 = 0 := by
  have hc : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ t in 𝓝 (0 : ℝ), f s t = g t :=
    Filter.Eventually.curry_nhds h
  constructor
  · have e : (fun s => f s 0) =ᶠ[𝓝 0] fun _ => g 0 := by
      filter_upwards [hc] with s hs
      exact hs.self_of_nhds
    rw [e.deriv_eq]
    simp
  · have e : (fun s => deriv (fun t => f s t) 0) =ᶠ[𝓝 0] fun _ => deriv g 0 := by
      filter_upwards [hc] with s hs
      exact Filter.EventuallyEq.deriv_eq hs
    rw [e.deriv_eq]
    simp
private lemma derivs_eq_zero_of_const_second {f : ℝ → ℝ → ℂ} {g : ℝ → ℂ}
    (h : ∀ᶠ w : ℝ × ℝ in 𝓝 (0, 0), f w.1 w.2 = g w.1) :
    deriv (fun t => f 0 t) 0 = 0 ∧ deriv (fun s => deriv (fun t => f s t) 0) 0 = 0 := by
  have hc : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ t in 𝓝 (0 : ℝ), f s t = g s :=
    Filter.Eventually.curry_nhds h
  constructor
  · have e : (fun t => f 0 t) =ᶠ[𝓝 0] fun _ => g 0 := hc.self_of_nhds
    rw [e.deriv_eq]
    simp
  · have e : (fun s => deriv (fun t => f s t) 0) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hc] with s hs
      have e' : (fun t => f s t) =ᶠ[𝓝 0] fun _ => g s := hs
      rw [e'.deriv_eq]
      simp
    rw [e.deriv_eq]
    simp
section Matrices
variable {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
private lemma sum_sum_ite_eq (x : ι' → ι → ℂ) (p : ι') (q : ι) :
    (∑ c, ∑ c₁, if c = p ∧ c₁ = q then x c c₁ else 0) = x p q := by
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
private lemma differentiableAt_of_entries {g : ℂ → Matrix ι' ι ℂ} {w : ℂ}
    (h : ∀ p q, DifferentiableAt ℂ (fun ζ => g ζ p q) w) :
    DifferentiableAt ℂ g w ∧ ∀ p q, deriv g w p q = deriv (fun ζ => g ζ p q) w := by
  have e : g = fun ζ => ∑ p, ∑ q, g ζ p q • Matrix.single p q (1 : ℂ) := by
    funext ζ
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    exact (sum_sum_ite_eq (g ζ) p q).symm
  have hd : HasDerivAt (fun ζ => ∑ p, ∑ q, g ζ p q • Matrix.single p q (1 : ℂ))
      (∑ p, ∑ q, deriv (fun ζ => g ζ p q) w • Matrix.single p q (1 : ℂ)) w :=
    HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun q _ =>
      (h p q).hasDerivAt.smul_const _
  rw [← e] at hd
  refine ⟨hd.differentiableAt, fun p q => ?_⟩
  rw [hd.deriv]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  exact sum_sum_ite_eq (fun c c₁ => deriv (fun ζ => g ζ c c₁) w) p q
private lemma deriv_ofReal_eq {f f' : ℂ → ℂ} (hd : DifferentiableAt ℂ f 0)
    {F : ℝ → ℂ} (he : ∀ᶠ s in 𝓝 (0 : ℝ), F s = f s) (hf : f' = f) :
    deriv F 0 = deriv f' 0 := by
  subst hf
  have h1 : HasDerivAt (fun s : ℝ => f' s) (deriv f' 0) 0 := by
    have : HasDerivAt f' (deriv f' 0) ((0 : ℝ) : ℂ) := by simpa using hd.hasDerivAt
    exact this.comp_ofReal
  have h2 : F =ᶠ[𝓝 0] fun s : ℝ => f' s := he
  rw [h2.deriv_eq]
  exact h1.deriv
private lemma cauchy_bounds_matrix {B : ℂ → ℂ → Matrix ι' ι ℂ} {T : ℝ → ℝ → Matrix ι' ι ℂ}
    {R₁ R₂ C : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (h₁ : ∀ p q σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → DifferentiableAt ℂ (fun σ' => B σ' τ p q) σ)
    (h₂ : ∀ p q σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → DifferentiableAt ℂ (fun τ' => B σ τ' p q) τ)
    (hb : ∀ σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → ‖B σ τ‖ ≤ C)
    (heq : ∀ᶠ w : ℝ × ℝ in 𝓝 (0, 0), T w.1 w.2 = B w.1 w.2)
    (hsm : ∀ p q, ContDiffAt ℝ 2 (fun w : ℝ × ℝ => T w.1 w.2 p q) 0) :
    ‖T 0 0‖ ≤ C ∧ ‖derivFirst T‖ ≤ 2 * C / R₁ ∧ ‖derivSecond T‖ ≤ 2 * C / R₂ ∧
      ‖derivMixed T‖ ≤ 8 * C / (R₁ * R₂) := by
  have z₁ : ‖(0 : ℂ)‖ < R₁ := by simpa using hR₁
  have z₂ : ‖(0 : ℂ)‖ < R₂ := by simpa using hR₂
  have v₁ : ∀ σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → DifferentiableAt ℂ (fun σ' => B σ' τ) σ :=
    fun σ τ a b => (differentiableAt_of_entries fun p q => h₁ p q σ τ a b).1
  have v₂ : ∀ σ τ, ‖σ‖ < R₁ → ‖τ‖ < R₂ → DifferentiableAt ℂ (fun τ' => B σ τ') τ :=
    fun σ τ a b => (differentiableAt_of_entries fun p q => h₂ p q σ τ a b).1
  have hcurry : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ t in 𝓝 (0 : ℝ), T s t = B s t :=
    Filter.Eventually.curry_nhds heq
  have e00 : T 0 0 = B 0 0 := by simpa using heq.self_of_nhds
  have eS : ∀ᶠ s in 𝓝 (0 : ℝ), T s 0 = B s 0 := by
    filter_upwards [hcurry] with s hs
    simpa using hs.self_of_nhds
  have eT : ∀ᶠ t in 𝓝 (0 : ℝ), T 0 t = B 0 t := by
    filter_upwards [hcurry.self_of_nhds] with t ht
    simpa using ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00]
    exact hb 0 0 z₁ z₂
  · have e : derivFirst T = deriv (fun σ => B σ 0) 0 := by
      ext p q
      rw [(differentiableAt_of_entries fun p q => h₁ p q 0 0 z₁ z₂).2 p q]
      refine deriv_ofReal_eq (h₁ p q 0 0 z₁ z₂) ?_ rfl
      filter_upwards [eS] with s hs
      rw [hs]
    rw [e]
    refine norm_deriv_le_of_ball hR₁ (fun w hw => v₁ w 0 (by simpa using hw) z₂) fun w hw =>
      hb w 0 (by simpa using hw) z₂
  · have e : derivSecond T = deriv (fun τ => B 0 τ) 0 := by
      ext p q
      rw [(differentiableAt_of_entries fun p q => h₂ p q 0 0 z₁ z₂).2 p q]
      refine deriv_ofReal_eq (h₂ p q 0 0 z₁ z₂) ?_ rfl
      filter_upwards [eT] with s hs
      rw [hs]
    rw [e]
    refine norm_deriv_le_of_ball hR₂ (fun w hw => v₂ 0 w z₁ (by simpa using hw)) fun w hw =>
      hb 0 w z₁ (by simpa using hw)
  · set Hh : ℝ → Matrix ι' ι ℂ := fun s p q => deriv (fun t => T s t p q) 0 with hHh
    set H : ℂ → Matrix ι' ι ℂ := fun σ => deriv (fun τ => B σ τ) 0 with hH
    have small : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ‖(s : ℂ)‖ < R₁ / 2 := by
      have : Filter.Tendsto (fun s : ℝ => ‖(s : ℂ)‖) (𝓝 0) (𝓝 0) := by
        have h : Continuous fun s : ℝ => ‖(s : ℂ)‖ := by fun_prop
        simpa using h.tendsto 0
      exact this.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < R₁ / 2))
    have eH : ∀ᶠ s in 𝓝 (0 : ℝ), Hh s = H s := by
      filter_upwards [hcurry, small] with s hs hsmall
      have hs₁ : ‖(s : ℂ)‖ < R₁ := by linarith
      ext p q
      simp only [hHh, hH]
      rw [(differentiableAt_of_entries fun p q => h₂ p q s 0 hs₁ z₂).2 p q]
      refine deriv_ofReal_eq (h₂ p q s 0 hs₁ z₂) ?_ rfl
      filter_upwards [hs] with t ht
      rw [ht]
    have e0 : Hh 0 = H 0 := by simpa using eH.self_of_nhds
    have lim : Filter.Tendsto (fun s : ℝ => ((s : ℂ)⁻¹) • (Hh s - Hh 0)) (𝓝[≠] 0)
        (𝓝 (derivMixed T)) := by
      refine tendsto_pi_nhds.2 fun p => tendsto_pi_nhds.2 fun q => ?_
      have hd : HasDerivAt (fun s => Hh s p q) (derivMixed T p q) 0 :=
        (IsC2At.differentiableAt_deriv (hsm p q)).hasDerivAt
      have := hasDerivAt_iff_tendsto_slope.1 hd
      refine this.congr fun s => ?_
      simp [slope, Matrix.smul_apply, Matrix.sub_apply]
    have bound : ∀ᶠ s : ℝ in 𝓝[≠] (0 : ℝ), ‖((s : ℂ)⁻¹) • (Hh s - Hh 0)‖ ≤ 8 * C / (R₁ * R₂) := by
      filter_upwards [self_mem_nhdsWithin, eH.filter_mono nhdsWithin_le_nhds,
        small.filter_mono nhdsWithin_le_nhds] with s hs0 hs hsm'
      have h0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
      have hn : 0 < ‖(s : ℂ)‖ := norm_pos_iff.2 h0
      rw [norm_smul, hs, e0, norm_inv]
      have := norm_deriv_sub_le hR₁ hR₂ (G := B) v₁ v₂ hb (σ := s) hsm'.le
      calc ‖(s : ℂ)‖⁻¹ * ‖H s - H 0‖ ≤ ‖(s : ℂ)‖⁻¹ * (8 * C / (R₁ * R₂) * ‖(s : ℂ)‖) := by gcongr
        _ = 8 * C / (R₁ * R₂) := by field_simp
    exact le_of_tendsto lim.norm bound
abbrev _root_.YangMills.SharedProofs.p47968 := @cauchy_bounds_matrix
end Matrices
section Main
variable {L n k : ℕ} {I ι : Type}
private lemma norm_blockBetween_le [Fintype ι] [DecidableEq ι] (c : ι → Vertex L n k k)
    (A : Matrix ι ι ℂ) (y' y : Vertex L n k k) : ‖blockBetween c c A y' y‖ ≤ ‖A‖ := by
  classical
  have e : blockBetween c c A y' y =
      Matrix.diagonal (fun p => if c p = y' then (1 : ℂ) else 0) * A *
        Matrix.diagonal (fun q => if c q = y then (1 : ℂ) else 0) := by
    ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [blockBetween]
    by_cases h1 : c p = y' <;> by_cases h2 : c q = y <;> simp [h1, h2]
  have d : ∀ (P : ι → Prop) [DecidablePred P],
      ‖(Matrix.diagonal (fun p => if P p then (1 : ℂ) else 0) : Matrix ι ι ℂ)‖ ≤ 1 := by
    intro P _
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    split_ifs <;> simp
  rw [e]
  calc _ ≤ ‖Matrix.diagonal (fun p => if c p = y' then (1 : ℂ) else 0) * A‖ *
        ‖(Matrix.diagonal (fun q => if c q = y then (1 : ℂ) else 0) : Matrix ι ι ℂ)‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(Matrix.diagonal (fun p => if c p = y' then (1 : ℂ) else 0) : Matrix ι ι ℂ)‖ * ‖A‖) * 1 :=
        mul_le_mul (Matrix.l2_opNorm_mul _ _) (d _) (norm_nonneg _) (by positivity)
    _ ≤ (1 * ‖A‖) * 1 := by gcongr; exact d _
    _ = ‖A‖ := by ring
private lemma norm_blockBetween_eq_zero [Fintype ι] [DecidableEq ι] {c : ι → Vertex L n k k}
    {A : Matrix ι ι ℂ} {u v : Vertex L n k k} (h : ∀ p q, c p = u → c q = v → A p q = 0) :
    ‖blockBetween c c A u v‖ = 0 := by
  classical
  have e : blockBetween c c A u v = 0 := by
    ext p q
    simp only [blockBetween, Matrix.zero_apply]
    split_ifs with hh
    · exact h p q hh.1 hh.2
    · rfl
  rw [e, norm_zero]
private lemma cellDist_nonneg (y y' : Vertex L n k k) : 0 ≤ cellDist y y' := by apply _root_.YangMills.SharedProofs.p2231 <;> assumption
private lemma cellDist_comm (u v : Vertex L n k k) : cellDist u v = cellDist v u := by apply _root_.YangMills.SharedProofs.p19196 <;> assumption
variable [Fintype I] [Fintype ι] [DecidableEq ι]
private def planeCombo (x x' : I → ℝ) (σ τ : ℂ) : I → ℂ :=
  fun i => σ * (x i : ℂ) + τ * (x' i : ℂ)
private lemma planeCombo_ofReal (x x' : I → ℝ) (s t : ℝ) :
    planeCombo x x' (s : ℂ) (t : ℂ) = complexifyCoords (s • x + t • x') := by
  funext i
  simp [planeCombo, complexifyCoords]
private lemma planeCombo_mem_ball {x x' : I → ℝ} (hx : ∀ i, |x i| ≤ 1) (hx' : ∀ i, |x' i| ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ) {σ τ : ℂ} (hσ : ‖σ‖ < ρ / 2) (hτ : ‖τ‖ < ρ / 2) :
    planeCombo x x' σ τ ∈ Metric.ball (0 : I → ℂ) ρ := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff hρ]
  intro i
  have h1 : ‖σ * (x i : ℂ)‖ ≤ ‖σ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (hx i)
  have h2 : ‖τ * (x' i : ℂ)‖ ≤ ‖τ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (hx' i)
  calc ‖planeCombo x x' σ τ i‖ ≤ ‖σ * (x i : ℂ)‖ + ‖τ * (x' i : ℂ)‖ := norm_add_le _ _
    _ < ρ := by linarith
private lemma eventually_small_pair {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ w : ℝ × ℝ in 𝓝 (0, 0), ‖(w.1 : ℂ)‖ < ρ / 2 ∧ ‖(w.2 : ℂ)‖ < ρ / 2 := by
  have h1 : Continuous fun w : ℝ × ℝ => ‖(w.1 : ℂ)‖ := by fun_prop
  have h2 : Continuous fun w : ℝ × ℝ => ‖(w.2 : ℂ)‖ := by fun_prop
  have e1 := h1.tendsto ((0 : ℝ), (0 : ℝ))
  have e2 := h2.tendsto ((0 : ℝ), (0 : ℝ))
  simp only [Complex.ofReal_zero, norm_zero] at e1 e2
  exact (e1.eventually (gt_mem_nhds (by positivity))).and
    (e2.eventually (gt_mem_nhds (by positivity)))
private lemma differentiable_planeCombo_left (x x' : I → ℝ) (τ : ℂ) :
    Differentiable ℂ (fun σ' : ℂ => planeCombo x x' σ' τ) := by
  unfold planeCombo
  fun_prop
private lemma differentiable_planeCombo_right (x x' : I → ℝ) (σ : ℂ) :
    Differentiable ℂ (fun τ' : ℂ => planeCombo x x' σ τ') := by
  unfold planeCombo
  fun_prop
private lemma contDiffAt_entry {f : (I → ℂ) → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 ρ)) (x x' : I → ℝ) :
    ContDiffAt ℝ 2 (fun w : ℝ × ℝ => f (complexifyCoords (w.1 • x + w.2 • x'))) 0 := by
  have h0 : AnalyticAt ℂ f 0 := hf 0 (Metric.mem_ball_self hρ)
  have h1 : AnalyticAt ℝ f 0 := h0.restrictScalars
  let Φ : ℝ × ℝ →L[ℝ] (I → ℂ) := ContinuousLinearMap.pi fun i =>
    (x i : ℂ) • (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
      (x' i : ℂ) • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hΦ : ∀ w, Φ w = complexifyCoords (w.1 • x + w.2 • x') := by
    intro w
    funext i
    simp [Φ, complexifyCoords, mul_comm]
  have h00 : Φ 0 = 0 := map_zero Φ
  have h2 : AnalyticAt ℝ (f ∘ Φ) 0 :=
    AnalyticAt.comp (by rw [h00]; exact h1) (Φ.analyticAt 0)
  have h3 : ContDiffAt ℝ 2 (f ∘ Φ) 0 := h2.contDiffAt
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  simp [Function.comp, hΦ]
set_option maxHeartbeats 1600000 in
private lemma isLocalAlongCellPair_of_family {ρ C r : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    {M : ℝ} (hM : 0 < M) (hM₀ : C * Real.exp (3 * r) ≤ M)
    (hM₁ : 2 * C / (ρ / 2) * Real.exp (3 * r) ≤ M)
    (hM₂ : 8 * C / ((ρ / 2) * (ρ / 2)) * Real.exp (3 * r) ≤ M)
    (e : I → Vertex L n k k) (c : ι → Vertex L n k k) (F : (I → ℂ) → Matrix ι ι ℂ)
    (T : ℝ → ℝ → Matrix ι ι ℂ) (x x' : I → ℝ) (y y' : Vertex L n k k)
    (hF : IsLocallyHolomorphicFamily e c c F ρ C r)
    (hx : ∀ i, |x i| ≤ 1) (hx' : ∀ i, |x' i| ≤ 1)
    (hc : ∀ i, e i ≠ y → x i = 0) (hc' : ∀ i, e i ≠ y' → x' i = 0)
    (hT : ∀ᶠ w : ℝ × ℝ in 𝓝 0, T w.1 w.2 = F (complexifyCoords (w.1 • x + w.2 • x'))) :
    IsLocalAlongCellPair c T y y' M 1 := by
  have hR : 0 < ρ / 2 := by positivity
  have hT' : ∀ᶠ w : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)),
      T w.1 w.2 = F (complexifyCoords (w.1 • x + w.2 • x')) := hT
  have hsm : ∀ p q, ContDiffAt ℝ 2 (fun w : ℝ × ℝ => T w.1 w.2 p q) 0 := by
    intro p q
    refine (contDiffAt_entry hρ (hF.holomorphic p q) x x').congr_of_eventuallyEq ?_
    filter_upwards [hT] with w hw
    rw [hw]
  have hpl : ∀ σ τ : ℂ, ‖σ‖ < ρ / 2 → ‖τ‖ < ρ / 2 →
      planeCombo x x' σ τ ∈ Metric.ball (0 : I → ℂ) ρ :=
    fun σ τ a b => planeCombo_mem_ball hx hx' hρ a b
  have hda : ∀ p q, ∀ z ∈ Metric.ball (0 : I → ℂ) ρ, DifferentiableAt ℂ (fun z => F z p q) z :=
    fun p q z hz => (hF.holomorphic p q z hz).differentiableAt
  obtain ⟨b₀, b₁, b₂, b₃⟩ := cauchy_bounds_matrix (B := fun σ τ => F (planeCombo x x' σ τ))
    (T := T) (R₁ := ρ / 2) (R₂ := ρ / 2) (C := C) hR hR
    (fun p q σ τ a b => DifferentiableAt.comp σ (hda p q _ (hpl σ τ a b))
      ((differentiable_planeCombo_left x x' τ) σ))
    (fun p q σ τ a b => DifferentiableAt.comp τ (hda p q _ (hpl σ τ a b))
      ((differentiable_planeCombo_right x x' σ) τ))
    (fun σ τ a b => hF.norm_le _ (hpl σ τ a b))
    (by
      filter_upwards [hT'] with w hw
      rw [hw, planeCombo_ofReal])
    hsm
  have sm := eventually_small_pair hρ
  have hz : ∀ w : ℝ × ℝ, ‖(w.1 : ℂ)‖ < ρ / 2 → ‖(w.2 : ℂ)‖ < ρ / 2 →
      complexifyCoords (w.1 • x + w.2 • x') ∈ Metric.ball (0 : I → ℂ) ρ := by
    intro w a b
    rw [← planeCombo_ofReal]
    exact hpl _ _ a b
  have hzero : ∀ p q, r < cellDist (c p) (c q) →
      ∀ᶠ w : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), T w.1 w.2 p q = (fun _ : ℝ => (0 : ℂ)) w.2 := by
    intro p q hd
    filter_upwards [hT', sm] with w hw hs
    rw [hw]
    exact hF.eq_zero_of_far _ (hz w hs.1 hs.2) p q hd
  have hnot_s : ∀ p q, r < cellDist (c p) y →
      ∀ᶠ w : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), T w.1 w.2 p q =
        (fun t : ℝ => F (planeCombo x x' 0 t) p q) w.2 := by
    intro p q hd
    filter_upwards [hT', sm] with w hw hs
    rw [hw, ← planeCombo_ofReal]
    refine hF.depends_near p q _ (hpl _ _ hs.1 hs.2) _ (hpl _ _ (by simpa using hR) hs.2)
      fun i hi => ?_
    have hne : e i ≠ y := by
      intro h
      rw [h, cellDist_comm] at hi
      exact absurd hd (not_lt.2 hi)
    simp [planeCombo, hc i hne]
  have hnot_t : ∀ p q, r < cellDist (c p) y' →
      ∀ᶠ w : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), T w.1 w.2 p q =
        (fun s : ℝ => F (planeCombo x x' s 0) p q) w.1 := by
    intro p q hd
    filter_upwards [hT', sm] with w hw hs
    rw [hw, ← planeCombo_ofReal]
    refine hF.depends_near p q _ (hpl _ _ hs.1 hs.2) _ (hpl _ _ hs.1 (by simpa using hR))
      fun i hi => ?_
    have hne : e i ≠ y' := by
      intro h
      rw [h, cellDist_comm] at hi
      exact absurd hd (not_lt.2 hi)
    simp [planeCombo, hc' i hne]
  have hexp : ∀ {a b d : ℝ}, 0 ≤ a → 0 ≤ d → d ≤ 3 * r → a * Real.exp (3 * r) ≤ b →
      a ≤ b * Real.exp (-d) := by
    intro a b d ha _ hd hab
    have h1 : Real.exp (d) ≤ Real.exp (3 * r) := Real.exp_le_exp.2 hd
    have h2 : a * Real.exp d ≤ b := (mul_le_mul_of_nonneg_left h1 ha).trans hab
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    exact h2
  have hnn₁ : 0 ≤ 2 * C / (ρ / 2) := by positivity
  have hnn₂ : 0 ≤ 8 * C / ((ρ / 2) * (ρ / 2)) := by positivity
  have e2 : ∀ a b : ℝ, M * Real.exp (-(1 * a)) * Real.exp (-(1 * b)) =
      M * Real.exp (-(a + b)) := by
    intro a b
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have e3 : ∀ a b d : ℝ, M * Real.exp (-(1 * a)) * (Real.exp (-(1 * b)) * Real.exp (-(1 * d))) =
      M * Real.exp (-(a + (b + d))) := by
    intro a b d
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  refine ⟨hsm, ?_, ?_, ?_, ?_⟩
  · intro u v
    by_cases hd : r < cellDist u v
    · rw [norm_blockBetween_eq_zero fun p q hp hq => ?_]
      · positivity
      · subst hp hq
        have := (hzero p q hd).self_of_nhds
        simpa using this
    · refine (norm_blockBetween_le c _ u v).trans (b₀.trans ?_)
      have := hexp hC (cellDist_nonneg u v) (by linarith [not_lt.1 hd]) hM₀
      simpa [one_mul] using this
  · intro u v
    have hw : cellDecayWeight 1 y u = Real.exp (-(1 * cellDist u y)) := rfl
    rw [hw, e2]
    by_cases hd : r < cellDist u v
    · rw [norm_blockBetween_eq_zero fun p q hp hq => ?_]
      · positivity
      · subst hp hq
        exact (derivs_eq_zero_of_const_first (f := fun s t => T s t p q) (g := fun _ => 0)
          (hzero p q hd)).1
    · by_cases hd' : r < cellDist u y
      · rw [norm_blockBetween_eq_zero fun p q hp hq => ?_]
        · positivity
        · subst hp hq
          exact (derivs_eq_zero_of_const_first (f := fun s t => T s t p q)
            (g := fun t : ℝ => F (planeCombo x x' 0 t) p q) (hnot_s p q hd')).1
      · refine (norm_blockBetween_le c _ u v).trans (b₁.trans ?_)
        exact hexp (d := cellDist u v + cellDist u y) hnn₁
          (add_nonneg (cellDist_nonneg _ _) (cellDist_nonneg _ _))
          (by linarith [not_lt.1 hd, not_lt.1 hd']) hM₁
  · intro u v
    have hw : cellDecayWeight 1 y' u = Real.exp (-(1 * cellDist u y')) := rfl
    rw [hw, e2]
    by_cases hd : r < cellDist u v
    · rw [norm_blockBetween_eq_zero fun p q hp hq => ?_]
      · positivity
      · subst hp hq
        exact (derivs_eq_zero_of_const_first (f := fun s t => T t s p q) (g := fun _ => 0)
          (by
            have h1 := hzero p q hd
            have h2 : Filter.Tendsto (Prod.swap : ℝ × ℝ → ℝ × ℝ) (𝓝 (0, 0)) (𝓝 (0, 0)) := by
              simpa using continuous_swap.tendsto ((0 : ℝ), (0 : ℝ))
            filter_upwards [h2.eventually h1] with w hw
            simpa using hw)).1
    · by_cases hd' : r < cellDist u y'
      · rw [norm_blockBetween_eq_zero fun p q hp hq => ?_]
        · positivity
        · subst hp hq
          exact (derivs_eq_zero_of_const_second (f := fun s t => T s t p q)
            (g := fun s : ℝ => F (planeCombo x x' s 0) p q) (hnot_t p q hd')).1
      · refine (norm_blockBetween_le c _ u v).trans (b₂.trans ?_)
        exact hexp (d := cellDist u v + cellDist u y') hnn₁
          (add_nonneg (cellDist_nonneg _ _) (cellDist_nonneg _ _))
          (by linarith [not_lt.1 hd, not_lt.1 hd']) hM₁
  · intro u v
    have hw : cellDecayWeight 1 y u = Real.exp (-(1 * cellDist u y)) := rfl
    have hw' : cellDecayWeight 1 y' u = Real.exp (-(1 * cellDist u y')) := rfl
    show _ ≤ M * Real.exp (-(1 * cellDist u v)) * (cellDecayWeight 1 y u * cellDecayWeight 1 y' u)
    rw [hw, hw', e3]
    by_cases hd : r < cellDist u v
    · rw [norm_blockBetween_eq_zero fun p q hp hq => ?_]
      · positivity
      · subst hp hq
        exact (derivs_eq_zero_of_const_first (f := fun s t => T s t p q) (g := fun _ => 0)
          (hzero p q hd)).2
    · by_cases hd' : r < cellDist u y
      · rw [norm_blockBetween_eq_zero fun p q hp hq => ?_]
        · positivity
        · subst hp hq
          exact (derivs_eq_zero_of_const_first (f := fun s t => T s t p q)
            (g := fun t : ℝ => F (planeCombo x x' 0 t) p q) (hnot_s p q hd')).2
      · by_cases hd'' : r < cellDist u y'
        · rw [norm_blockBetween_eq_zero fun p q hp hq => ?_]
          · positivity
          · subst hp hq
            exact (derivs_eq_zero_of_const_second (f := fun s t => T s t p q)
              (g := fun s : ℝ => F (planeCombo x x' s 0) p q) (hnot_t p q hd'')).2
        · refine (norm_blockBetween_le c _ u v).trans (b₃.trans ?_)
          exact hexp (d := cellDist u v + (cellDist u y + cellDist u y')) hnn₂
            (add_nonneg (cellDist_nonneg _ _)
              (add_nonneg (cellDist_nonneg _ _) (cellDist_nonneg _ _)))
            (by linarith [not_lt.1 hd, not_lt.1 hd', not_lt.1 hd'']) hM₂
end Main
theorem holomorphicFamiliesAreLocal : HolomorphicFamiliesAreLocal := by
  intro ρ C r hρ hC hr
  refine ⟨(C + 2 * C / (ρ / 2) + 8 * C / ((ρ / 2) * (ρ / 2)) + 1) * Real.exp (3 * r), 1,
    by positivity, one_pos, ?_⟩
  intro L n k I ι _ _ _ e c F T x x' y y' hF hx hx' hc hc' hT
  have hq : 0 ≤ 2 * C / (ρ / 2) := by positivity
  have hq' : 0 ≤ 8 * C / ((ρ / 2) * (ρ / 2)) := by positivity
  have he := Real.exp_pos (3 * r)
  exact isLocalAlongCellPair_of_family hρ hC hr (by positivity)
    (mul_le_mul_of_nonneg_right (by linarith) he.le)
    (mul_le_mul_of_nonneg_right (by linarith) he.le)
    (mul_le_mul_of_nonneg_right (by linarith) he.le) e c F T x x' y y' hF hx hx' hc hc' hT
end YangMills.Construction.RunningCouplingSlope.LocalityProof
end
