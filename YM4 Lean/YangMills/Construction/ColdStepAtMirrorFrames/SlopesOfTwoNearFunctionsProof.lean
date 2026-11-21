import YangMills.Construction.ColdStepAtMirrorFrames.SlopesOfTwoNearFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
theorem derivDiffBoundOfClose : DerivDiffBoundOfClose := by
  intro f₁ f₂ d₁ d₂ e₁ e₂ h M₀ M₂ hh hf₁ hf₂ hd₁ hd₂ he₁ he₂ h0 hh'
  have hM₂ : 0 ≤ M₂ := (abs_nonneg _).trans (he₁ 0 ⟨le_rfl, hh.le⟩)
  have hd : ∀ u ∈ Set.Icc (0 : ℝ) h, HasDerivWithinAt (fun s => d₁ s - d₂ s) (e₁ u - e₂ u) (Set.Icc 0 h) u :=
    fun u hu => ((hd₁ u hu).sub (hd₂ u hu)).hasDerivWithinAt
  have hdb : ∀ u ∈ Set.Icc (0 : ℝ) h, ‖e₁ u - e₂ u‖ ≤ 2 * M₂ := fun u hu => by
    rw [Real.norm_eq_abs]
    have := abs_sub (e₁ u) (e₂ u)
    have := he₁ u hu
    have := he₂ u hu
    linarith
  have hmove : ∀ u ∈ Set.Icc (0 : ℝ) h, |(d₁ u - d₂ u) - (d₁ 0 - d₂ 0)| ≤ 2 * M₂ * h := fun u hu => by
    have := (convex_Icc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le hd hdb
      (Set.left_mem_Icc.2 hh.le) hu
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hu.1] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_left hu.2 (by positivity)
  have hφ : ∀ u ∈ Set.Icc (0 : ℝ) h, HasDerivWithinAt (fun s => (f₁ s - f₂ s) - s * (d₁ 0 - d₂ 0))
      ((d₁ u - d₂ u) - (d₁ 0 - d₂ 0)) (Set.Icc 0 h) u := fun u hu => by
    have a := ((hf₁ u hu).sub (hf₂ u hu))
    have b := (hasDerivAt_id u).mul_const (d₁ 0 - d₂ 0)
    have := a.sub b
    simp only [id, one_mul] at this
    exact this.hasDerivWithinAt
  have hφb := (convex_Icc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le hφ
    (fun u hu => by rw [Real.norm_eq_abs]; exact hmove u hu)
    (Set.left_mem_Icc.2 hh.le) (Set.right_mem_Icc.2 hh.le)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_pos hh] at hφb
  have hkey : h * |d₁ 0 - d₂ 0| ≤ 2 * M₀ + 2 * M₂ * h * h := by
    have e : h * (d₁ 0 - d₂ 0) = (f₁ h - f₂ h) - (f₁ 0 - f₂ 0) -
        (((f₁ h - f₂ h) - h * (d₁ 0 - d₂ 0)) - ((f₁ 0 - f₂ 0) - 0 * (d₁ 0 - d₂ 0))) := by ring
    have : |h * (d₁ 0 - d₂ 0)| ≤ |f₁ h - f₂ h| + |f₁ 0 - f₂ 0| + 2 * M₂ * h * h := by
      rw [e]
      refine (abs_sub _ _).trans ?_
      have := abs_sub (f₁ h - f₂ h) (f₁ 0 - f₂ 0)
      linarith
    rw [abs_mul, abs_of_pos hh] at this
    linarith
  have : |d₁ 0 - d₂ 0| = h * |d₁ 0 - d₂ 0| / h := by field_simp
  rw [this, div_le_iff₀ hh]
  have : (2 * M₀ / h + 2 * M₂ * h) * h = 2 * M₀ + 2 * M₂ * h * h := by field_simp
  linarith
end YangMills.Construction.Calculus
end
