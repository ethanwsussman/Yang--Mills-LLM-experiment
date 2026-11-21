import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativeFromSecondDifferences
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology Metric
namespace YangMills.Construction.Analytic
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
private theorem hasDerivAt_comp_line {g : X → ℂ} {y : X} (hg : DifferentiableAt ℂ g y) (a : X) :
    HasDerivAt (fun w : ℂ => g (y + w • a)) (fderiv ℂ g y a) 0 := by
  have hline : HasDerivAt (fun w : ℂ => y + w • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const a).const_add y
  have h1 : HasFDerivAt g (fderiv ℂ g y) (y + (0 : ℂ) • a) := by
    simpa using hg.hasFDerivAt
  exact h1.comp_hasDerivAt (0 : ℂ) hline
private theorem analyticOnNhd_fderiv_apply {G : X → ℂ} {s : Set X} (hG : AnalyticOnNhd ℂ G s) (a : X) :
    AnalyticOnNhd ℂ (fun y => fderiv ℂ G y a) s := fun y hy =>
  ((ContinuousLinearMap.apply ℂ ℂ a).analyticAt _).comp (hG y hy).fderiv
private theorem norm_fderiv_fderiv_apply_le {G : X → ℂ} {ρ M : ℝ} {a b : X} (hM : 0 ≤ M)
    (hG : AnalyticOnNhd ℂ G (ball 0 ρ)) {t : X} (ht : t ∈ ball (0 : X) ρ)
    (hd : ∃ δ : ℝ, 0 < δ ∧ ∀ w₁ w₂ : ℂ, ‖w₁‖ < δ → ‖w₂‖ < δ →
      ‖G (t + w₁ • a + w₂ • b) - G (t + w₁ • a) - G (t + w₂ • b) + G t‖ ≤ M * ‖w₁‖ * ‖w₂‖) :
    ‖fderiv ℂ (fun s => fderiv ℂ G s a) t b‖ ≤ M := by
  obtain ⟨δ, hδ0, hδ⟩ := hd
  have hcont : Tendsto (fun w : ℂ => t + w • b) (𝓝 0) (𝓝 t) := by
    have : Continuous fun w : ℂ => t + w • b := by fun_prop
    simpa using this.tendsto 0
  have hnear : ∀ᶠ w : ℂ in 𝓝 0, t + w • b ∈ ball (0 : X) ρ :=
    hcont.eventually (isOpen_ball.mem_nhds ht)
  have hsmall : ∀ᶠ w : ℂ in 𝓝 0, ‖w‖ < δ := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ0] with w hw
    simpa using hw
  have hfirst : ∀ᶠ w₂ : ℂ in 𝓝 0, ‖fderiv ℂ G (t + w₂ • b) a - fderiv ℂ G t a‖ ≤ M * ‖w₂‖ := by
    filter_upwards [hnear, hsmall] with w₂ hin hw₂
    have h1 := hasDerivAt_comp_line (hG _ hin).differentiableAt a
    have h2 := hasDerivAt_comp_line (hG _ ht).differentiableAt a
    have h3 : HasDerivAt (fun w : ℂ => G (t + w₂ • b + w • a) - G (t + w • a))
        (fderiv ℂ G (t + w₂ • b) a - fderiv ℂ G t a) 0 := h1.sub h2
    refine h3.le_of_lip' (by positivity) ?_
    filter_upwards [hsmall] with w₁ hw₁
    have e := hδ w₁ w₂ hw₁ hw₂
    have e1 : t + w₂ • b + w₁ • a = t + w₁ • a + w₂ • b := by abel
    simp only [zero_smul, add_zero, sub_zero]
    rw [e1]
    calc ‖G (t + w₁ • a + w₂ • b) - G (t + w₁ • a) - (G (t + w₂ • b) - G t)‖
        = ‖G (t + w₁ • a + w₂ • b) - G (t + w₁ • a) - G (t + w₂ • b) + G t‖ := by
          congr 1
          ring
      _ ≤ M * ‖w₁‖ * ‖w₂‖ := e
      _ = M * ‖w₂‖ * ‖w₁‖ := by ring
  have h4 := hasDerivAt_comp_line (analyticOnNhd_fderiv_apply hG a t ht).differentiableAt b
  refine h4.le_of_lip' hM ?_
  filter_upwards [hfirst] with w hw
  simpa using hw
private theorem iteratedFDeriv_succ_apply_eq_fderiv_last {g : X → ℂ} {y : X} (hg : AnalyticAt ℂ g y) (n : ℕ)
    (v : Fin (n + 1) → X) :
    iteratedFDeriv ℂ (n + 1) g y v =
      iteratedFDeriv ℂ n (fun s => fderiv ℂ g s (v (Fin.last n))) y (Fin.init v) := by
  let ev : (X →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (v (Fin.last n))
  have hcd : ContDiffAt ℂ n (fderiv ℂ g) y := hg.fderiv.contDiffAt
  rw [iteratedFDeriv_succ_apply_right]
  have h3 := ev.iteratedFDeriv_comp_left hcd le_rfl
  rw [show (fun s => fderiv ℂ g s (v (Fin.last n))) = ev ∘ fderiv ℂ g from rfl, h3]
  rfl
private theorem exists_perm_to_last_two {n : ℕ} {i₁ i₂ : Fin (n + 2)} (h : i₁ ≠ i₂) :
    ∃ σ : Equiv.Perm (Fin (n + 2)), σ (Fin.last (n + 1)) = i₁ ∧ σ (Fin.last n).castSucc = i₂ := by
  have hpq : (Fin.last n).castSucc ≠ Fin.last (n + 1) := (Fin.castSucc_lt_last _).ne
  have hc : Equiv.swap (Fin.last (n + 1)) i₁ (Fin.last n).castSucc ≠ i₁ := by
    intro e
    apply hpq
    apply (Equiv.swap (Fin.last (n + 1)) i₁).injective
    rw [Equiv.swap_apply_left]
    exact e
  refine ⟨Equiv.swap (Equiv.swap (Fin.last (n + 1)) i₁ (Fin.last n).castSucc) i₂ *
    Equiv.swap (Fin.last (n + 1)) i₁, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hc.symm h
  · simp only [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_left _ _
private theorem prod_perm_castSucc_castSucc_eq {k : ℕ} (c : Fin (k + 2) → ℝ) {i₁ i₂ : Fin (k + 2)}
    (σ : Equiv.Perm (Fin (k + 2)))
    (h₁ : σ (Fin.last (k + 1)) = i₁) (h₂ : σ (Fin.last k).castSucc = i₂) :
    ∏ l : Fin k, c (σ l.castSucc.castSucc) = ∏ l ∈ (Finset.univ.erase i₁).erase i₂, c l := by
  let f : Fin (k + 2) → ℝ := fun l => if l = i₁ ∨ l = i₂ then 1 else c l
  have e1 : ∏ l ∈ (Finset.univ.erase i₁).erase i₂, c l = ∏ l ∈ (Finset.univ.erase i₁).erase i₂, f l := by
    refine Finset.prod_congr rfl fun l hl => ?_
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hl
    simp [f, hl.1, hl.2]
  have e2 : ∏ l ∈ (Finset.univ.erase i₁).erase i₂, f l = ∏ l ∈ Finset.univ.erase i₁, f l :=
    Finset.prod_erase _ (by simp [f])
  have e3 : ∏ l ∈ Finset.univ.erase i₁, f l = ∏ l, f l := Finset.prod_erase _ (by simp [f])
  have e4 : ∏ l, f (σ l) = ∏ l, f l := Equiv.prod_comp σ f
  rw [e1, e2, e3, ← e4, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, h₁, h₂]
  have f₁ : f i₁ = 1 := by simp [f]
  have f₂ : f i₂ = 1 := by simp [f]
  rw [f₁, f₂, mul_one, mul_one]
  refine Finset.prod_congr rfl fun l _ => ?_
  have n₁ : σ l.castSucc.castSucc ≠ i₁ := by
    rw [← h₁]
    exact fun e => (Fin.castSucc_lt_last _).ne (σ.injective e)
  have n₂ : σ l.castSucc.castSucc ≠ i₂ := by
    rw [← h₂]
    intro e
    have e' := Fin.castSucc_injective _ (σ.injective e)
    exact (Fin.castSucc_lt_last _).ne e'
  simp [f, n₁, n₂]
theorem mixedDerivativeOfSecondDifferences : mixedDerivativeOfSecondDifferencesStatement := by
  intro m k G ρ M v i₁ i₂ hne hρ hM hG hd
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_perm_to_last_two hne
  have h0 : (0 : Fin m → ℂ) ∈ ball (0 : Fin m → ℂ) ρ := by simpa using hρ
  have hLa := analyticOnNhd_fderiv_apply hG (v i₁)
  have hHa := analyticOnNhd_fderiv_apply hLa (v i₂)
  have hHb : ∀ t ∈ ball (0 : Fin m → ℂ) ρ,
      ‖fderiv ℂ (fun s => fderiv ℂ G s (v i₁)) t (v i₂)‖ ≤ M := fun t ht =>
    norm_fderiv_fderiv_apply_le hM hG ht (hd t ht)
  have hperm : iteratedFDeriv ℂ (k + 2) G 0 (v ∘ σ) = iteratedFDeriv ℂ (k + 2) G 0 v :=
    ContDiffAt.iteratedFDeriv_comp_perm (hG 0 h0).contDiffAt v σ
  have s1 := iteratedFDeriv_succ_apply_eq_fderiv_last (hG 0 h0) (k + 1) (v ∘ σ)
  have u1 : (v ∘ σ) (Fin.last (k + 1)) = v i₁ := by simp [hσ₁]
  rw [u1] at s1
  have s2 := iteratedFDeriv_succ_apply_eq_fderiv_last (hLa 0 h0) k (Fin.init (v ∘ σ))
  have u2 : Fin.init (v ∘ σ) (Fin.last k) = v i₂ := by simp [Fin.init, hσ₂]
  rw [u2] at s2
  have hb := norm_iteratedFDeriv_zero_apply_le_of_norm_le_on_ball k hρ hHa hHb (Fin.init (Fin.init (v ∘ σ)))
  rw [← hperm]
  refine (le_of_eq (congrArg norm (s1.trans s2))).trans (hb.trans (le_of_eq ?_))
  congr 1
  exact prod_perm_castSucc_castSucc_eq (fun l => ‖v l‖) σ hσ₁ hσ₂
end YangMills.Construction.Analytic
end
