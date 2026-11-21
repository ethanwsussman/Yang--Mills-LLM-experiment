import YangMills.Construction.HoleBesideASecondHole.APlaquetteAlongFourSegments
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace GroupPaths
theorem norm_prod_four_sub_linear_le (c₁ c₂ c₃ c₄ : ℍ[ℝ]) (h₁ : ‖c₁‖ ≤ 1) (h₂ : ‖c₂‖ ≤ 1) (h₃ : ‖c₃‖ ≤ 1) (h₄ : ‖c₄‖ ≤ 1) :
    ‖(1 + c₁) * (1 + c₂) * (1 + c₃) * (1 + c₄) - 1 - (c₁ + c₂ + c₃ + c₄)‖ ≤
      3 * (‖c₁‖ ^ 2 + ‖c₂‖ ^ 2 + ‖c₃‖ ^ 2 + ‖c₄‖ ^ 2) := by
  set d := c₁ + c₂ + c₁ * c₂ with hd
  set d' := c₃ + c₄ + c₃ * c₄ with hd'
  have e : (1 + c₁) * (1 + c₂) * (1 + c₃) * (1 + c₄) - 1 - (c₁ + c₂ + c₃ + c₄) =
      c₁ * c₂ + c₃ * c₄ + d * d' := by
    rw [hd, hd']
    noncomm_ring
  rw [e]
  have x1 := norm_nonneg c₁
  have x3 := norm_nonneg c₃
  have n12 : ‖c₁ * c₂‖ ≤ ‖c₁‖ * ‖c₂‖ := norm_mul_le _ _
  have n34 : ‖c₃ * c₄‖ ≤ ‖c₃‖ * ‖c₄‖ := norm_mul_le _ _
  have nd : ‖d‖ ≤ 2 * ‖c₁‖ + ‖c₂‖ := by
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le c₁ c₂
    have h : ‖c₁‖ * ‖c₂‖ ≤ ‖c₁‖ * 1 := mul_le_mul_of_nonneg_left h₂ x1
    linarith
  have nd' : ‖d'‖ ≤ 2 * ‖c₃‖ + ‖c₄‖ := by
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le c₃ c₄
    have h : ‖c₃‖ * ‖c₄‖ ≤ ‖c₃‖ * 1 := mul_le_mul_of_nonneg_left h₄ x3
    linarith
  have ndd : ‖d * d'‖ ≤ (2 * ‖c₁‖ + ‖c₂‖) * (2 * ‖c₃‖ + ‖c₄‖) :=
    (norm_mul_le _ _).trans (mul_le_mul nd nd' (norm_nonneg _) (by positivity))
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le (c₁ * c₂) (c₃ * c₄)
  nlinarith [sq_nonneg (‖c₁‖ - ‖c₂‖), sq_nonneg (‖c₃‖ - ‖c₄‖),
    sq_nonneg (2 * ‖c₁‖ + ‖c₂‖ - 2 * ‖c₃‖ - ‖c₄‖), sq_nonneg (‖c₁‖ - 2 * ‖c₂‖), sq_nonneg (‖c₃‖ - 2 * ‖c₄‖)]
theorem coe_inv_eq_star (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
theorem eq_smul_add_linear_rest (r₁ r₂ s₃ s₄ e₁ e₂ f₃ f₄ : ℍ[ℝ]) (t₁ t₂ t₃ t₄ : ℝ) (Z Z' w w' : ℍ[ℝ])
    (hZ : Z = w + (r₁ + r₂ + s₃ + s₄))
    (hZ' : Z' = w' + ((t₁ • r₁ + e₁) + (t₂ • r₂ + e₂) + (t₃ • s₃ + f₃) + (t₄ • s₄ + f₄))) :
    Z' = t₁ • Z - t₁ • w + (t₂ - t₁) • r₂ + (t₃ - t₁) • s₃ + (t₄ - t₁) • s₄ + (e₁ + e₂ + f₃ + f₄) + w' := by
  subst hZ hZ'
  module
theorem norm_seven_terms_le (a b c d e f g : ℍ[ℝ]) :
    ‖a - b + c + d + e + f + g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  have h1 := norm_add_le (a - b + c + d + e + f) g
  have h2 := norm_add_le (a - b + c + d + e) f
  have h3 := norm_add_le (a - b + c + d) e
  have h4 := norm_add_le (a - b + c) d
  have h5 := norm_add_le (a - b) c
  have h6 := norm_sub_le a b
  linarith
theorem norm_smul_add_le_of_small (t : ℝ) (r e : ℍ[ℝ]) (h0 : 0 ≤ t) (h1 : t ≤ 1) (hr : ‖r‖ ≤ 1 / 2)
    (he : ‖e‖ ≤ ‖r‖ ^ 2) :
    ‖t • r + e‖ ≤ 3 / 2 * ‖r‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  have x := norm_nonneg r
  nlinarith
theorem sq_le_of_le_three_halves (a b : ℝ) (h0 : 0 ≤ a) (h1 : 0 ≤ b) (h2 : a ≤ 3 / 2 * b) :
    a ^ 2 ≤ 9 / 4 * b ^ 2 := by
  nlinarith
theorem norm_smul_le_of_mem_unitInterval (t : ℝ) (Z : ℍ[ℝ]) (h0 : 0 ≤ t) (h1 : t ≤ 1) : ‖t • Z‖ ≤ ‖Z‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  have := norm_nonneg Z
  nlinarith
theorem norm_perturbed_plaquette_sub_one_le (r₁ r₂ r₃ r₄ e₁ e₂ e₃ e₄ : ℍ[ℝ]) (t₁ t₂ t₃ t₄ : ℝ)
    (a₁ : 0 ≤ t₁) (b₁ : t₁ ≤ 1) (a₂ : 0 ≤ t₂) (b₂ : t₂ ≤ 1) (a₃ : 0 ≤ t₃) (b₃ : t₃ ≤ 1) (a₄ : 0 ≤ t₄) (b₄ : t₄ ≤ 1)
    (h₁ : ‖r₁‖ ≤ 1 / 2) (h₂ : ‖r₂‖ ≤ 1 / 2) (h₃ : ‖r₃‖ ≤ 1 / 2) (h₄ : ‖r₄‖ ≤ 1 / 2)
    (n₁ : ‖e₁‖ ≤ ‖r₁‖ ^ 2) (n₂ : ‖e₂‖ ≤ ‖r₂‖ ^ 2) (n₃ : ‖e₃‖ ≤ ‖r₃‖ ^ 2) (n₄ : ‖e₄‖ ≤ ‖r₄‖ ^ 2) :
    ‖(1 + (t₁ • r₁ + e₁)) * (1 + (t₂ • r₂ + e₂)) * (1 + star (t₃ • r₃ + e₃)) * (1 + star (t₄ • r₄ + e₄)) - 1‖ ≤
      ‖(1 + r₁) * (1 + r₂) * (1 + star r₃) * (1 + star r₄) - 1‖ +
        (|t₂ - t₁| * ‖r₂‖ + |t₃ - t₁| * ‖r₃‖ + |t₄ - t₁| * ‖r₄‖) +
        11 * (‖r₁‖ ^ 2 + ‖r₂‖ ^ 2 + ‖r₃‖ ^ 2 + ‖r₄‖ ^ 2) := by
  have m₁ := norm_smul_add_le_of_small t₁ r₁ e₁ a₁ b₁ h₁ n₁
  have m₂ := norm_smul_add_le_of_small t₂ r₂ e₂ a₂ b₂ h₂ n₂
  have m₃ := norm_smul_add_le_of_small t₃ r₃ e₃ a₃ b₃ h₃ n₃
  have m₄ := norm_smul_add_le_of_small t₄ r₄ e₄ a₄ b₄ h₄ n₄
  have x₁ := norm_nonneg r₁
  have x₂ := norm_nonneg r₂
  have x₃ := norm_nonneg r₃
  have x₄ := norm_nonneg r₄
  have y₁ := sq_nonneg ‖r₁‖
  have y₂ := sq_nonneg ‖r₂‖
  have y₃ := sq_nonneg ‖r₃‖
  have y₄ := sq_nonneg ‖r₄‖
  have hOld := norm_prod_four_sub_linear_le r₁ r₂ (star r₃) (star r₄) (by linarith) (by linarith)
    (by rw [Quaternion.norm_star]; linarith) (by rw [Quaternion.norm_star]; linarith)
  rw [Quaternion.norm_star, Quaternion.norm_star] at hOld
  generalize hc₁ : t₁ • r₁ + e₁ = c₁ at *
  generalize hc₂ : t₂ • r₂ + e₂ = c₂ at *
  generalize hc₃ : t₃ • r₃ + e₃ = c₃ at *
  generalize hc₄ : t₄ • r₄ + e₄ = c₄ at *
  have hNew := norm_prod_four_sub_linear_le c₁ c₂ (star c₃) (star c₄) (by linarith) (by linarith)
    (by rw [Quaternion.norm_star]; linarith) (by rw [Quaternion.norm_star]; linarith)
  rw [Quaternion.norm_star, Quaternion.norm_star] at hNew
  generalize hZ : (1 + r₁) * (1 + r₂) * (1 + star r₃) * (1 + star r₄) - 1 = Z at *
  generalize hZ' : (1 + c₁) * (1 + c₂) * (1 + star c₃) * (1 + star c₄) - 1 = Z' at *
  have hstar : ∀ (t : ℝ) (r : ℍ[ℝ]), star (t • r) = t • star r := by
    intro t r
    ext <;> simp
  have hdec := eq_smul_add_linear_rest r₁ r₂ (star r₃) (star r₄) e₁ e₂ (star e₃) (star e₄) t₁ t₂ t₃ t₄ Z Z'
    (Z - (r₁ + r₂ + star r₃ + star r₄)) (Z' - (c₁ + c₂ + star c₃ + star c₄)) (by abel) (by
      have h3 : star c₃ = t₃ • star r₃ + star e₃ := by
        rw [← hc₃, star_add, hstar]
      have h4 : star c₄ = t₄ • star r₄ + star e₄ := by
        rw [← hc₄, star_add, hstar]
      rw [← hc₁, ← hc₂, h3, h4]
      abel)
  rw [hdec]
  refine (norm_seven_terms_le _ _ _ _ _ _ _).trans ?_
  have hZn := norm_smul_le_of_mem_unitInterval t₁ Z a₁ b₁
  have hwn := norm_smul_le_of_mem_unitInterval t₁ (Z - (r₁ + r₂ + star r₃ + star r₄)) a₁ b₁
  have s₁ := sq_le_of_le_three_halves _ _ (norm_nonneg _) x₁ m₁
  have s₂ := sq_le_of_le_three_halves _ _ (norm_nonneg _) x₂ m₂
  have s₃ := sq_le_of_le_three_halves _ _ (norm_nonneg _) x₃ m₃
  have s₄ := sq_le_of_le_three_halves _ _ (norm_nonneg _) x₄ m₄
  have hd₂ : ‖(t₂ - t₁) • r₂‖ = |t₂ - t₁| * ‖r₂‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have hd₃ : ‖(t₃ - t₁) • star r₃‖ = |t₃ - t₁| * ‖r₃‖ := by
    rw [norm_smul, Real.norm_eq_abs, Quaternion.norm_star]
  have hd₄ : ‖(t₄ - t₁) • star r₄‖ = |t₄ - t₁| * ‖r₄‖ := by
    rw [norm_smul, Real.norm_eq_abs, Quaternion.norm_star]
  have hee : ‖e₁ + e₂ + star e₃ + star e₄‖ ≤ ‖r₁‖ ^ 2 + ‖r₂‖ ^ 2 + ‖r₃‖ ^ 2 + ‖r₄‖ ^ 2 := by
    have h1 := norm_add_le (e₁ + e₂ + star e₃) (star e₄)
    have h2 := norm_add_le (e₁ + e₂) (star e₃)
    have h3 := norm_add_le e₁ e₂
    rw [Quaternion.norm_star] at h1 h2
    linarith
  rw [hd₂, hd₃, hd₄]
  linarith
theorem plaquetteAlongPathsBound_holds : PlaquetteAlongPathsBound := by
  intro Φ hΦ t₁ t₂ t₃ t₄ q₁ q₂ q₃ q₄ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ h₁ h₂ h₃ h₄
  have f : ∀ (t : ℝ) (q : UnitQuaternion), 0 ≤ t → t ≤ 1 → ‖(q : ℍ[ℝ]) - 1‖ ≤ 1 / 2 → ∃ e : ℍ[ℝ],
      ((Φ t q : UnitQuaternion) : ℍ[ℝ]) = 1 + (t • ((q : ℍ[ℝ]) - 1) + e) ∧ ‖e‖ ≤ ‖(q : ℍ[ℝ]) - 1‖ ^ 2 := by
    intro t q a b h
    refine ⟨((Φ t q : UnitQuaternion) : ℍ[ℝ]) - (1 + t • ((q : ℍ[ℝ]) - 1)), by abel, hΦ t q a b h⟩
  obtain ⟨e₁, f₁, n₁⟩ := f t₁ q₁ a₁ b₁ h₁
  obtain ⟨e₂, f₂, n₂⟩ := f t₂ q₂ a₂ b₂ h₂
  obtain ⟨e₃, f₃, n₃⟩ := f t₃ q₃ a₃ b₃ h₃
  obtain ⟨e₄, f₄, n₄⟩ := f t₄ q₄ a₄ b₄ h₄
  have E1 : ((Φ t₁ q₁ * Φ t₂ q₂ * (Φ t₃ q₃)⁻¹ * (Φ t₄ q₄)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (1 + (t₁ • ((q₁ : ℍ[ℝ]) - 1) + e₁)) * (1 + (t₂ • ((q₂ : ℍ[ℝ]) - 1) + e₂)) *
        (1 + star (t₃ • ((q₃ : ℍ[ℝ]) - 1) + e₃)) * (1 + star (t₄ • ((q₄ : ℍ[ℝ]) - 1) + e₄)) := by
    simp only [Submonoid.coe_mul, coe_inv_eq_star]
    rw [f₁, f₂, f₃, f₄]
    simp only [star_add, star_one]
  have g : ∀ q : UnitQuaternion, (q : ℍ[ℝ]) = 1 + ((q : ℍ[ℝ]) - 1) := fun q => by abel
  have g' : ∀ q : UnitQuaternion, star (q : ℍ[ℝ]) = 1 + star ((q : ℍ[ℝ]) - 1) := fun q => by
    rw [star_sub, star_one]
    abel
  have E2 : ((q₁ * q₂ * q₃⁻¹ * q₄⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (1 + ((q₁ : ℍ[ℝ]) - 1)) * (1 + ((q₂ : ℍ[ℝ]) - 1)) * (1 + star ((q₃ : ℍ[ℝ]) - 1)) *
        (1 + star ((q₄ : ℍ[ℝ]) - 1)) := by
    simp only [Submonoid.coe_mul, coe_inv_eq_star]
    rw [← g q₁, ← g q₂, ← g' q₃, ← g' q₄]
  rw [E1, E2]
  exact norm_perturbed_plaquette_sub_one_le _ _ _ _ e₁ e₂ e₃ e₄ t₁ t₂ t₃ t₄ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄
    h₁ h₂ h₃ h₄ n₁ n₂ n₃ n₄
end GroupPaths
end YangMills.Construction
end
