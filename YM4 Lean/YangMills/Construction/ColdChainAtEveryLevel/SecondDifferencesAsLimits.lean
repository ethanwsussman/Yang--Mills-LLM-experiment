import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
open Filter Topology
theorem tendsto_secondDifference_div_sq {f : ℝ × ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    Tendsto (fun ε : ℝ => (f (ε, ε) - f (ε, 0) - f (0, ε) + f (0, 0)) / ε ^ 2) (𝓝[>] 0)
      (𝓝 (deriv (fun τ : ℝ => deriv (fun σ : ℝ => f (τ, σ)) 0) 0)) := by
  set f' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fderiv ℝ f with hf'
  have h1 : ContDiffAt ℝ 1 f' 0 := hf.fderiv_right (by norm_num)
  set D : ℝ × ℝ → (ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ)) := fderiv ℝ f' with hD
  have hDc : ContinuousAt D 0 := (h1.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hev1 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), DifferentiableAt ℝ f x := by
    have := hf.eventually (by simp)
    filter_upwards [this] with x hx using hx.differentiableAt (by norm_num)
  have hev2 : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), DifferentiableAt ℝ f' x := by
    have := h1.eventually (by simp)
    filter_upwards [this] with x hx using hx.differentiableAt (by norm_num)
  have hline : ∀ {v : ℝ × ℝ} {x : ℝ × ℝ} {t : ℝ}, ∀ {φ : ℝ × ℝ → ℝ} {φ' : ℝ × ℝ →L[ℝ] ℝ},
      HasFDerivAt φ φ' x → ∀ c : ℝ × ℝ, x = c + t • v →
        HasDerivAt (fun r : ℝ => φ (c + r • v)) (φ' v) t := by
    intro v x t φ φ' hφ c hx
    have hl : HasDerivAt (fun r : ℝ => c + r • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add c
    have := HasFDerivAt.comp_hasDerivAt t (hx ▸ hφ) hl
    exact this
  set e₁ : ℝ × ℝ := (1, 0) with he₁
  set e₂ : ℝ × ℝ := (0, 1) with he₂
  have hval : deriv (fun τ : ℝ => deriv (fun σ : ℝ => f (τ, σ)) 0) 0 = D 0 e₁ e₂ := by
    have hinner : (fun τ : ℝ => deriv (fun σ : ℝ => f (τ, σ)) 0) =ᶠ[𝓝 0] fun τ => f' (τ, 0) e₂ := by
      have hc : Tendsto (fun τ : ℝ => ((τ, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
        have : Continuous (fun τ : ℝ => ((τ, 0) : ℝ × ℝ)) := by fun_prop
        exact this.tendsto' 0 0 rfl
      filter_upwards [hc.eventually hev1] with τ hτ
      have := hline (v := e₂) (t := 0) hτ.hasFDerivAt ((τ, 0) : ℝ × ℝ) (by simp)
      have e : (fun r : ℝ => f (((τ, 0) : ℝ × ℝ) + r • e₂)) = fun σ => f (τ, σ) := by
        funext r
        simp [he₂]
      rw [e] at this
      exact this.deriv
    rw [hinner.deriv_eq]
    have hd : HasFDerivAt f' (D 0) 0 := (hev2.self_of_nhds).hasFDerivAt
    have hap : HasFDerivAt (fun x => f' x e₂) ((ContinuousLinearMap.apply ℝ ℝ e₂).comp (D 0)) 0 :=
      (ContinuousLinearMap.apply ℝ ℝ e₂).hasFDerivAt.comp 0 hd
    have := hline (v := e₁) (t := 0) hap (0 : ℝ × ℝ) (by simp)
    have e : (fun r : ℝ => f' ((0 : ℝ × ℝ) + r • e₁) e₂) = fun τ => f' (τ, 0) e₂ := by
      funext r
      simp [he₁]
    rw [e] at this
    simpa using this.deriv
  rw [hval]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
  obtain ⟨r', hr', hcont⟩ := (Metric.continuousAt_iff (f := D) (a := 0)).1 (by exact hDc) (η / (‖e₁‖ * ‖e₂‖ + 1)) (by positivity)
  refine ⟨min r r', lt_min hr hr', fun ε hε hεd => ?_⟩
  have hε0 : 0 < ε := hε
  have hεr : ε < min r r' := by
    have := hεd
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0] at this
    exact this
  have hin : ∀ x : ℝ × ℝ, 0 ≤ x.1 → x.1 ≤ ε → 0 ≤ x.2 → x.2 ≤ ε → dist x 0 < min r r' := by
    intro x a b c d
    have : dist x (0 : ℝ × ℝ) ≤ ε := by
      rw [Prod.dist_eq]
      refine max_le ?_ ?_
      · simpa [Real.dist_eq, abs_of_nonneg a] using b
      · simpa [Real.dist_eq, abs_of_nonneg c] using d
    linarith
  have hgood : ∀ x : ℝ × ℝ, 0 ≤ x.1 → x.1 ≤ ε → 0 ≤ x.2 → x.2 ≤ ε →
      DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ f' x := fun x a b c d =>
    hball ((hin x a b c d).trans_le (min_le_left _ _))
  have hsecond : ∃ y ∈ Set.Ioo 0 ε, f' (ε, y) e₂ - f' (0, y) e₂ =
      ((f (ε, ε) - f (0, ε)) - (f (ε, 0) - f (0, 0))) / (ε - 0) := by
    refine exists_hasDerivAt_eq_slope (fun σ => f (ε, σ) - f (0, σ))
      (fun y => f' (ε, y) e₂ - f' (0, y) e₂) hε0 ?_ ?_
    · intro y hy
      have a1 := ((hgood (ε, y) hε0.le le_rfl hy.1 hy.2).1).continuousAt
      have a2 := ((hgood (0, y) le_rfl hε0.le hy.1 hy.2).1).continuousAt
      have c1 : ContinuousAt (fun σ : ℝ => ((ε, σ) : ℝ × ℝ)) y := by fun_prop
      have c2 : ContinuousAt (fun σ : ℝ => ((0, σ) : ℝ × ℝ)) y := by fun_prop
      exact ((ContinuousAt.comp (f := fun σ : ℝ => ((ε, σ) : ℝ × ℝ)) a1 c1).sub
        (ContinuousAt.comp (f := fun σ : ℝ => ((0, σ) : ℝ × ℝ)) a2 c2)).continuousWithinAt
    · intro y hy
      have a1 := hline (v := e₂) (t := y) ((hgood (ε, y) hε0.le le_rfl hy.1.le hy.2.le).1).hasFDerivAt
        ((ε, 0) : ℝ × ℝ) (by simp [he₂])
      have a2 := hline (v := e₂) (t := y) ((hgood (0, y) le_rfl hε0.le hy.1.le hy.2.le).1).hasFDerivAt
        ((0, 0) : ℝ × ℝ) (by simp [he₂])
      have e1 : (fun r : ℝ => f (((ε, 0) : ℝ × ℝ) + r • e₂)) = fun σ => f (ε, σ) := by
        funext r
        simp [he₂]
      have e2 : (fun r : ℝ => f (((0, 0) : ℝ × ℝ) + r • e₂)) = fun σ => f (0, σ) := by
        funext r
        simp [he₂]
      rw [e1] at a1
      rw [e2] at a2
      exact a1.sub a2
  obtain ⟨y, hy, hy1⟩ := hsecond
  have hfirst : ∃ x ∈ Set.Ioo 0 ε, D (x, y) e₁ e₂ = (f' (ε, y) e₂ - f' (0, y) e₂) / (ε - 0) := by
    refine exists_hasDerivAt_eq_slope (fun τ => f' (τ, y) e₂) (fun x => D (x, y) e₁ e₂) hε0 ?_ ?_
    · intro x hx
      have a1 := ((hgood (x, y) hx.1 hx.2 hy.1.le hy.2.le).2).continuousAt
      have c1 : ContinuousAt (fun τ : ℝ => ((τ, y) : ℝ × ℝ)) x := by fun_prop
      have a2 := ContinuousAt.comp (f := fun τ : ℝ => ((τ, y) : ℝ × ℝ)) a1 c1
      exact ((ContinuousLinearMap.apply ℝ ℝ e₂).continuous.continuousAt.comp a2).continuousWithinAt
    · intro x hx
      have hd : HasFDerivAt f' (D (x, y)) (x, y) :=
        ((hgood (x, y) hx.1.le hx.2.le hy.1.le hy.2.le).2).hasFDerivAt
      have hap : HasFDerivAt (fun x => f' x e₂) ((ContinuousLinearMap.apply ℝ ℝ e₂).comp (D (x, y))) (x, y) :=
        (ContinuousLinearMap.apply ℝ ℝ e₂).hasFDerivAt.comp (x, y) hd
      have := hline (v := e₁) (t := x) hap ((0, y) : ℝ × ℝ) (by simp [he₁])
      have e : (fun r : ℝ => f' (((0, y) : ℝ × ℝ) + r • e₁) e₂) = fun τ => f' (τ, y) e₂ := by
        funext r
        simp [he₁]
      rw [e] at this
      simpa using this
  obtain ⟨x, hx, hx1⟩ := hfirst
  have hεne : ε ≠ 0 := hε0.ne'
  have hmain : (f (ε, ε) - f (ε, 0) - f (0, ε) + f (0, 0)) / ε ^ 2 = D (x, y) e₁ e₂ := by
    rw [hx1, hy1]
    simp only [sub_zero]
    field_simp
    ring
  rw [hmain, Real.dist_eq]
  have hxy : dist ((x, y) : ℝ × ℝ) 0 < r' :=
    (hin (x, y) hx.1.le hx.2.le hy.1.le hy.2.le).trans_le (min_le_right _ _)
  have hc : ‖D (x, y) - D 0‖ < η / (‖e₁‖ * ‖e₂‖ + 1) :=
    lt_of_eq_of_lt (dist_eq_norm (D (x, y)) (D 0)).symm (hcont hxy)
  have h3 : D (x, y) e₁ e₂ - D 0 e₁ e₂ = (D (x, y) - D 0) e₁ e₂ := by simp
  rw [h3]
  have h4 : |(D (x, y) - D 0) e₁ e₂| ≤ ‖D (x, y) - D 0‖ * ‖e₁‖ * ‖e₂‖ :=
    ((D (x, y) - D 0).le_opNorm₂ e₁ e₂)
  have h6 : ‖D (x, y) - D 0‖ * (‖e₁‖ * ‖e₂‖ + 1) < η := by
    rwa [lt_div_iff₀ (by positivity)] at hc
  have h7 : 0 ≤ ‖D (x, y) - D 0‖ := ContinuousLinearMap.opNorm_nonneg _
  nlinarith
end YangMills.Construction.Calculus
end
