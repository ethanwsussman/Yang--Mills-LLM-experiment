import YangMills.Construction.Dirichlet.LiftDerivativeBounds
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
open YangMills.Construction.Dirichlet.CoverCount
noncomputable section
namespace YangMills.Construction.Dirichlet.LiftDerivatives
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
structure SecondOrderBound (f : E → ℝ) (v : E) (a b c : ℝ) : Prop where
  contDiffAt : ContDiffAt ℝ ∞ f v
  abs_le : |f v| ≤ a
  fderiv_le : ‖fderiv ℝ f v‖ ≤ b
  fderiv2_le : ‖fderiv ℝ (fderiv ℝ f) v‖ ≤ c
theorem eventually_hasFDerivAt_of_contDiffAt {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) :
    ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y := by
  have h1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  filter_upwards [h1.eventually (by simp)] with y hy
  exact (hy.differentiableAt (by simp)).hasFDerivAt
theorem hasFDerivAt_fderiv_of_contDiffAt {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x := by
  have h2 : ContDiffAt ℝ 2 f x := hf.of_le ENat.LEInfty.out
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := h2.fderiv_right (by norm_num)
  exact (h1.differentiableAt (by simp)).hasFDerivAt
theorem SecondOrderBound.weaken {f : E → ℝ} {x : E} {a b c a' b' c' : ℝ}
    (h : SecondOrderBound f x a b c) (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    SecondOrderBound f x a' b' c' :=
  ⟨h.contDiffAt, h.abs_le.trans ha, h.fderiv_le.trans hb, h.fderiv2_le.trans hc⟩
theorem SecondOrderBound.congr_eventually {f g : E → ℝ} {x : E} {a b c : ℝ}
    (h : SecondOrderBound g x a b c) (hfg : f =ᶠ[𝓝 x] g) : SecondOrderBound f x a b c := by
  refine ⟨h.contDiffAt.congr_of_eventuallyEq hfg, ?_, ?_, ?_⟩
  · rw [hfg.eq_of_nhds]; exact h.abs_le
  · rw [hfg.fderiv_eq]; exact h.fderiv_le
  · rw [hfg.fderiv.fderiv_eq]; exact h.fderiv2_le
theorem secondOrderBound_const_zero (x : E) :
    SecondOrderBound (fun _ : E => (0 : ℝ)) x 0 0 0 := by
  refine ⟨contDiffAt_const, by simp, by simp, ?_⟩
  have h1 : fderiv ℝ (fun _ : E => (0 : ℝ)) = fun _ => 0 := by
    funext y; simp
  have h2 : fderiv ℝ (fun _ : E => (0 : E →L[ℝ] ℝ)) x = 0 := by simp
  rw [h1, h2, ContinuousLinearMap.opNorm_zero]
theorem SecondOrderBound.add_fun {f g : E → ℝ} {x : E} {a b c a' b' c' : ℝ}
    (hf : SecondOrderBound f x a b c) (hg : SecondOrderBound g x a' b' c') :
    SecondOrderBound (fun y => f y + g y) x (a + a') (b + b') (c + c') := by
  have hEq : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x] fun y => fderiv ℝ f y + fderiv ℝ g y := by
    filter_upwards [eventually_hasFDerivAt_of_contDiffAt hf.contDiffAt,
      eventually_hasFDerivAt_of_contDiffAt hg.contDiffAt] with y h1 h2
    exact (h1.add h2).fderiv
  have hD := (hasFDerivAt_fderiv_of_contDiffAt hf.contDiffAt).add
    (hasFDerivAt_fderiv_of_contDiffAt hg.contDiffAt)
  refine ⟨hf.contDiffAt.add hg.contDiffAt,
    (abs_add_le _ _).trans (add_le_add hf.abs_le hg.abs_le), ?_, ?_⟩
  · rw [hEq.eq_of_nhds]
    exact (norm_add_le _ _).trans (add_le_add hf.fderiv_le hg.fderiv_le)
  · rw [hEq.fderiv_eq]
    have h2 := hD.fderiv
    refine (le_of_eq (congrArg Norm.norm h2)).trans ?_
    exact (norm_add_le _ _).trans (add_le_add hf.fderiv2_le hg.fderiv2_le)
theorem SecondOrderBound.finset_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {x : E}
    {a b c : ι → ℝ} (h : ∀ i ∈ s, SecondOrderBound (f i) x (a i) (b i) (c i)) :
    SecondOrderBound (fun y => ∑ i ∈ s, f i y) x (∑ i ∈ s, a i) (∑ i ∈ s, b i)
      (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using secondOrderBound_const_zero x
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add_fun
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem SecondOrderBound.comp_real {s : E → ℝ} {x : E} {a b c : ℝ}
    (hs : SecondOrderBound s x a b c) {φ φ₁ : ℝ → ℝ} {φ₂ p₀ p₁ p₂ : ℝ}
    (hφ : ContDiffAt ℝ ∞ φ (s x)) (h₀ : |φ (s x)| ≤ p₀)
    (hd : ∀ᶠ t in 𝓝 (s x), HasDerivAt φ (φ₁ t) t) (hd₂ : HasDerivAt φ₁ φ₂ (s x))
    (h₁ : |φ₁ (s x)| ≤ p₁) (h₂ : |φ₂| ≤ p₂) :
    SecondOrderBound (fun y => φ (s y)) x p₀ (p₁ * b) (p₁ * c + p₂ * b ^ 2) := by
  have hp₁ : 0 ≤ p₁ := (abs_nonneg _).trans h₁
  have hp₂ : 0 ≤ p₂ := (abs_nonneg _).trans h₂
  have hb : 0 ≤ b := (norm_nonneg _).trans hs.fderiv_le
  have hcont : ContinuousAt s x := hs.contDiffAt.continuousAt
  have hEq : fderiv ℝ (fun y => φ (s y)) =ᶠ[𝓝 x] fun y => φ₁ (s y) • fderiv ℝ s y := by
    filter_upwards [eventually_hasFDerivAt_of_contDiffAt hs.contDiffAt, hcont.eventually hd]
      with y h1 h2
    exact (h2.comp_hasFDerivAt y h1).fderiv
  have hs1 : HasFDerivAt s (fderiv ℝ s x) x :=
    (eventually_hasFDerivAt_of_contDiffAt hs.contDiffAt).self_of_nhds
  have hα : HasFDerivAt (fun y => φ₁ (s y)) (φ₂ • fderiv ℝ s x) x := hd₂.comp_hasFDerivAt x hs1
  have hD := hα.smul (hasFDerivAt_fderiv_of_contDiffAt hs.contDiffAt)
  refine ⟨hφ.comp x hs.contDiffAt, h₀, ?_, ?_⟩
  · rw [hEq.eq_of_nhds, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul h₁ hs.fderiv_le (norm_nonneg _) hp₁
  · rw [hEq.fderiv_eq]
    have h2 := hD.fderiv
    refine (le_of_eq (congrArg Norm.norm h2)).trans ((norm_add_le _ _).trans (add_le_add ?_ ?_))
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul h₁ hs.fderiv2_le (norm_nonneg _) hp₁
    · rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs, pow_two,
        ← mul_assoc]
      exact mul_le_mul (mul_le_mul h₂ hs.fderiv_le (norm_nonneg _) hp₂) hs.fderiv_le
        (norm_nonneg _) (mul_nonneg hp₂ hb)
end Calculus
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
theorem continuous_torusProj : Continuous (torusProj d S) :=
  continuous_pi fun μ => (AddCircle.continuous_mk' S).comp (continuous_apply μ)
end YangMills.Construction.Dirichlet.LiftDerivatives
