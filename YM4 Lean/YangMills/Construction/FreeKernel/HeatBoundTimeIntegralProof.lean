import YangMills.Construction.FreeKernel.HeatBoundTimeIntegral
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.HeatTimeIntegral
open MeasureTheory
def heatBoundIntegrand (k : ℕ) (R T : ℝ) : ℝ :=
  (max T 1) ^ (-(k : ℝ) / 2) * Real.exp (-R / Real.sqrt (max T 1))
lemma continuous_heatBoundIntegrand (k : ℕ) (R : ℝ) : Continuous (heatBoundIntegrand k R) := by
  have hmax : Continuous fun T : ℝ => max T 1 := continuous_id.max continuous_const
  have hpos : ∀ T : ℝ, 0 < max T 1 := fun T => lt_of_lt_of_le one_pos (le_max_right _ _)
  unfold heatBoundIntegrand
  refine (hmax.rpow_const fun T => Or.inl (hpos T).ne').mul (Real.continuous_exp.comp ?_)
  exact continuous_const.div (Real.continuous_sqrt.comp hmax)
    fun T => (Real.sqrt_pos.mpr (hpos T)).ne'
lemma heatBoundIntegrand_le_const (k : ℕ) {R : ℝ} (hR : 0 ≤ R) (T : ℝ) :
    heatBoundIntegrand k R T ≤ Real.exp 1 * k.factorial * ((R + 1) ^ k)⁻¹ := by
  unfold heatBoundIntegrand
  set t := max T 1 with ht
  have ht1 : 1 ≤ t := le_max_right _ _
  have ht0 : 0 < t := by linarith
  set s := Real.sqrt t with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr ht1
  have hs0 : 0 < s := by linarith
  have hcancel : t ^ (-(k : ℝ) / 2) * s ^ k = 1 := by
    have hpow : s ^ k = t ^ ((k : ℝ) / 2) := by
      rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      congr 1
      ring
    rw [hpow, ← Real.rpow_add ht0, show -(k : ℝ) / 2 + (k : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  have hb : 0 ≤ (R + 1) / s := by positivity
  have hexp : ((R + 1) / s) ^ k / k.factorial ≤ Real.exp ((R + 1) / s) :=
    Real.pow_div_factorial_le_exp _ hb k
  have hsplit : Real.exp (-R / s) = Real.exp (1 / s) * (Real.exp ((R + 1) / s))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hone : Real.exp (1 / s) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by rw [div_le_one hs0]; exact hs1)
  have hinv : (Real.exp ((R + 1) / s))⁻¹ ≤ k.factorial * s ^ k * ((R + 1) ^ k)⁻¹ := by
    have hpos : 0 < ((R + 1) / s) ^ k / k.factorial := by positivity
    calc (Real.exp ((R + 1) / s))⁻¹ ≤ (((R + 1) / s) ^ k / k.factorial)⁻¹ := inv_anti₀ hpos hexp
      _ = k.factorial * s ^ k * ((R + 1) ^ k)⁻¹ := by
        rw [div_pow]
        field_simp
  rw [hsplit]
  calc t ^ (-(k : ℝ) / 2) * (Real.exp (1 / s) * (Real.exp ((R + 1) / s))⁻¹)
      ≤ t ^ (-(k : ℝ) / 2) * (Real.exp 1 * (k.factorial * s ^ k * ((R + 1) ^ k)⁻¹)) := by
        gcongr
    _ = (t ^ (-(k : ℝ) / 2) * s ^ k) * (Real.exp 1 * k.factorial * ((R + 1) ^ k)⁻¹) := by ring
    _ = Real.exp 1 * k.factorial * ((R + 1) ^ k)⁻¹ := by rw [hcancel, one_mul]
lemma heatBoundIntegrand_le_rpow (k : ℕ) {R T : ℝ} (hR : 0 ≤ R) (hT : 1 ≤ T) :
    heatBoundIntegrand k R T ≤ T ^ (-(k : ℝ) / 2) := by
  unfold heatBoundIntegrand
  rw [max_eq_left hT]
  have hp : 0 ≤ T ^ (-(k : ℝ) / 2) := by positivity
  have he : Real.exp (-R / Real.sqrt T) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (by positivity)
  exact mul_le_of_le_one_right hp he
lemma heatBoundIntegrand_nonneg (k : ℕ) (R T : ℝ) : 0 ≤ heatBoundIntegrand k R T := by
  unfold heatBoundIntegrand
  positivity
lemma neg_half_cast_lt_neg_one {k : ℕ} (hk : 3 ≤ k) : -(k : ℝ) / 2 < -1 := by
  have : (3 : ℝ) ≤ k := by exact_mod_cast hk
  linarith
lemma integrableOn_Ioi_heatBoundIntegrand {k : ℕ} (hk : 3 ≤ k) {R b : ℝ} (hR : 0 ≤ R)
    (hb : 1 ≤ b) : IntegrableOn (heatBoundIntegrand k R) (Set.Ioi b) := by
  have hdom : IntegrableOn (fun T : ℝ => T ^ (-(k : ℝ) / 2)) (Set.Ioi b) :=
    integrableOn_Ioi_rpow_of_lt (neg_half_cast_lt_neg_one hk) (by linarith)
  refine Integrable.mono' hdom (continuous_heatBoundIntegrand k R).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun T hT => ?_)
  have hT1 : 1 ≤ T := hb.trans (le_of_lt hT)
  rw [Real.norm_of_nonneg (heatBoundIntegrand_nonneg k R T)]
  exact heatBoundIntegrand_le_rpow k hR hT1
lemma integrableOn_Ioc_heatBoundIntegrand (k : ℕ) (R b : ℝ) :
    IntegrableOn (heatBoundIntegrand k R) (Set.Ioc 0 b) :=
  ((continuous_heatBoundIntegrand k R).integrableOn_Icc (a := 0) (b := b)).mono_set
    Set.Ioc_subset_Icc_self
theorem timeIntegralOfHeatBound_proof : TimeIntegralOfHeatBound := by
  intro k hk
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < (k : ℝ) - 2 := by linarith
  refine ⟨Real.exp 1 * k.factorial + 2 / ((k : ℝ) - 2), by positivity, fun R hR => ?_⟩
  have hM1 : 1 ≤ R + 1 := by linarith
  have hM0 : 0 < R + 1 := by linarith
  have hM2 : 1 ≤ (R + 1) ^ 2 := one_le_pow₀ hM1
  have hM20 : 0 < (R + 1) ^ 2 := by positivity
  have hlow := integrableOn_Ioc_heatBoundIntegrand k R ((R + 1) ^ 2)
  have hhigh := integrableOn_Ioi_heatBoundIntegrand hk hR hM2
  have hunion : Set.Ioc 0 ((R + 1) ^ 2) ∪ Set.Ioi ((R + 1) ^ 2) = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hM20.le
  have hint : IntegrableOn (heatBoundIntegrand k R) (Set.Ioi 0) := by
    rw [← hunion]
    exact hlow.union hhigh
  refine ⟨hint, ?_⟩
  change ∫ T in Set.Ioi (0 : ℝ), heatBoundIntegrand k R T ≤ _
  have hsplit : ∫ T in Set.Ioi (0 : ℝ), heatBoundIntegrand k R T =
      (∫ T in Set.Ioc 0 ((R + 1) ^ 2), heatBoundIntegrand k R T) +
        ∫ T in Set.Ioi ((R + 1) ^ 2), heatBoundIntegrand k R T := by
    rw [← hunion]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hlow hhigh
  have hbelow : ∫ T in Set.Ioc 0 ((R + 1) ^ 2), heatBoundIntegrand k R T ≤
      Real.exp 1 * k.factorial * ((R + 1) ^ k)⁻¹ * (R + 1) ^ 2 := by
    have hconst : IntegrableOn (fun _ : ℝ => Real.exp 1 * k.factorial * ((R + 1) ^ k)⁻¹)
        (Set.Ioc 0 ((R + 1) ^ 2)) := continuous_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    calc ∫ T in Set.Ioc 0 ((R + 1) ^ 2), heatBoundIntegrand k R T
        ≤ ∫ _ in Set.Ioc 0 ((R + 1) ^ 2), Real.exp 1 * k.factorial * ((R + 1) ^ k)⁻¹ :=
          setIntegral_mono hlow hconst fun T => heatBoundIntegrand_le_const k hR T
      _ = Real.exp 1 * k.factorial * ((R + 1) ^ k)⁻¹ * (R + 1) ^ 2 := by
          rw [setIntegral_const]
          simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hM20.le]
          ring
  have habove : ∫ T in Set.Ioi ((R + 1) ^ 2), heatBoundIntegrand k R T ≤
      -((R + 1) ^ 2) ^ (-(k : ℝ) / 2 + 1) / (-(k : ℝ) / 2 + 1) := by
    rw [← integral_Ioi_rpow_of_lt (neg_half_cast_lt_neg_one hk) hM20]
    refine setIntegral_mono_on hhigh
      (integrableOn_Ioi_rpow_of_lt (neg_half_cast_lt_neg_one hk) hM20) measurableSet_Ioi
      fun T hT => ?_
    exact heatBoundIntegrand_le_rpow k hR (hM2.trans (le_of_lt hT))
  have hpow₁ : ((R + 1) ^ k)⁻¹ * (R + 1) ^ 2 = (R + 1) ^ (2 - (k : ℝ)) := by
    rw [Real.rpow_sub hM0, Real.rpow_natCast, Real.rpow_two]
    field_simp
  have hpow₂ : ((R + 1) ^ 2) ^ (-(k : ℝ) / 2 + 1) = (R + 1) ^ (2 - (k : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hM0.le]
    congr 1
    ring
  have hfrac : -((R + 1) ^ 2) ^ (-(k : ℝ) / 2 + 1) / (-(k : ℝ) / 2 + 1) =
      2 / ((k : ℝ) - 2) * (R + 1) ^ (2 - (k : ℝ)) := by
    rw [hpow₂, show -(k : ℝ) / 2 + 1 = -(((k : ℝ) - 2) / 2) by ring, neg_div_neg_eq,
      div_div_eq_mul_div]
    ring
  rw [hsplit]
  calc (∫ T in Set.Ioc 0 ((R + 1) ^ 2), heatBoundIntegrand k R T) +
        ∫ T in Set.Ioi ((R + 1) ^ 2), heatBoundIntegrand k R T
      ≤ Real.exp 1 * k.factorial * ((R + 1) ^ k)⁻¹ * (R + 1) ^ 2 +
          -((R + 1) ^ 2) ^ (-(k : ℝ) / 2 + 1) / (-(k : ℝ) / 2 + 1) := add_le_add hbelow habove
    _ = (Real.exp 1 * k.factorial + 2 / ((k : ℝ) - 2)) * (R + 1) ^ (2 - (k : ℝ)) := by
        rw [hfrac, mul_assoc (Real.exp 1 * k.factorial), hpow₁]
        ring
end YangMills.Construction.FreeKernel.HeatTimeIntegral
end
