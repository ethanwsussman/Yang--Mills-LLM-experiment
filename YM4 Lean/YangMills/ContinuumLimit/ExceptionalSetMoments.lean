import YangMills.Construction.TheStatementsProvedTogether.FromProductsUpOneStepProof
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace YangMills.Formulation

/-- Restricting a squared terminal response to a rare event, using the fourth
moment of its score under the same normalized law. -/
theorem terminal_bad_second_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : Set Ω) (R S : Ω → ℝ) {A M U : ℝ} (hM : 0 ≤ M)
    (hR : ∀ᵐ ω ∂μ, |R ω| ≤ A * S ω)
    (hscore : (∫⁻ ω, ENNReal.ofReal (S ω ^ 4) ∂μ) ≤ ENNReal.ofReal M)
    (hbad : μ B ≤ ENNReal.ofReal (Real.exp (-U))) :
    (∫⁻ ω in B, ENNReal.ofReal (R ω ^ 2) ∂μ) ≤
      ENNReal.ofReal (A ^ 2 * (1 + M) * Real.exp (-U / 2)) := by
  let t := Real.exp (U / 2)
  have ht : 0 < t := Real.exp_pos _
  let v := A ^ 2 / t
  have hv : 0 ≤ v := div_nonneg (sq_nonneg _) ht.le
  let a := A ^ 2 * t
  have ha : 0 ≤ a := mul_nonneg (sq_nonneg _) ht.le
  have point : ∀ᵐ ω ∂μ.restrict B, ENNReal.ofReal (R ω ^ 2) ≤
      ENNReal.ofReal a + ENNReal.ofReal v * ENNReal.ofReal (S ω ^ 4) := by
    filter_upwards [ae_restrict_of_ae hR] with ω hw
    rw [← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_add ha (mul_nonneg hv (by positivity))]
    apply ENNReal.ofReal_le_ofReal
    have hs : S ω ^ 2 ≤ t + S ω ^ 4 / t := by
      have h : S ω ^ 2 - t ≤ S ω ^ 4 / t := (le_div_iff₀ ht).mpr (by
        nlinarith [sq_nonneg (S ω ^ 2 - t), mul_nonneg (sq_nonneg (S ω)) ht.le])
      linarith
    have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg A)
    have hr := pow_le_pow_left₀ (abs_nonneg (R ω)) hw 2
    rw [sq_abs, mul_pow] at hr
    calc R ω ^ 2 ≤ A ^ 2 * S ω ^ 2 := hr
      _ ≤ A ^ 2 * (t + S ω ^ 4 / t) := hs'
      _ = a + v * S ω ^ 4 := by dsimp [a, v]; ring
  have hmass := setLIntegral_le_lintegral (μ := μ) B (fun ω => ENNReal.ofReal (S ω ^ 4))
  calc
    _ ≤ ∫⁻ ω in B, ENNReal.ofReal a + ENNReal.ofReal v * ENNReal.ofReal (S ω ^ 4) ∂μ :=
      lintegral_mono_ae point
    _ = ENNReal.ofReal a * μ B + ENNReal.ofReal v * ∫⁻ ω in B, ENNReal.ofReal (S ω ^ 4) ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal (Real.exp (-U)) + ENNReal.ofReal v * ENNReal.ofReal M :=
      add_le_add (mul_le_mul_right hbad _) (mul_le_mul_right (hmass.trans hscore) _)
    _ = _ := by
      rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hv,
        ← ENNReal.ofReal_add (mul_nonneg ha (Real.exp_pos _).le) (mul_nonneg hv hM)]
      congr 1
      dsimp [a, v, t]
      have he : Real.exp (U / 2) * Real.exp (-U) = Real.exp (-U / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      have hie : (Real.exp (U / 2))⁻¹ = Real.exp (-U / 2) := by rw [← Real.exp_neg]; congr 1; ring
      rw [div_eq_mul_inv (A ^ 2), hie]
      linear_combination A ^ 2 * he

/-- The two terminal score means in the separation error cost at most the sum
of their normalized second moments. -/
theorem terminal_score_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S T : Ω → ℝ) (hS : Measurable S) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hs : (∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ) ≤ ENNReal.ofReal M)
    (ht : (∫⁻ ω, ENNReal.ofReal (T ω ^ 2) ∂μ) ≤ ENNReal.ofReal N) :
    (∫⁻ ω, ENNReal.ofReal |S ω * T ω| ∂μ) ≤ ENNReal.ofReal (M + N) := by
  rw [ENNReal.ofReal_add hM hN]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) + ENNReal.ofReal (T ω ^ 2) ∂μ := by
      apply lintegral_mono
      intro ω
      change ENNReal.ofReal |S ω * T ω| ≤ ENNReal.ofReal (S ω ^ 2) + ENNReal.ofReal (T ω ^ 2)
      rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_mul]
      nlinarith [sq_nonneg (|S ω| - |T ω|), sq_abs (S ω), sq_abs (T ω),sq_nonneg (S ω),sq_nonneg (T ω)]
    _ ≤ _ := by rw [lintegral_add_left ((hS.pow_const 2).ennreal_ofReal)]; exact add_le_add hs ht

end YangMills.Formulation


