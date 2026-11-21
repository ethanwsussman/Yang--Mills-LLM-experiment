import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace UnitCurves
open BlockAverages
theorem inner_eq_re_mul_star (p q : ℍ[ℝ]) : inner ℝ p q = (q * star p).re := by
  rw [real_inner_comm, Quaternion.inner_def]
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
variable {γ : ℝ → ℍ[ℝ]} {γ' : ℍ[ℝ]}
theorem hasDerivAt_norm_of_ne_zero (hγ : HasDerivAt γ γ' 0) (hne : γ 0 ≠ 0) :
    HasDerivAt (fun t => ‖γ t‖) (inner ℝ (γ 0) γ' / ‖γ 0‖) 0 := by
  have hsq : HasDerivAt (fun t => ‖γ t‖ ^ 2) (2 * inner ℝ (γ 0) γ') 0 := hγ.norm_sq
  have hn : ‖γ 0‖ ≠ 0 := norm_ne_zero_iff.2 hne
  have hroot := hsq.sqrt (pow_ne_zero 2 hn)
  have hfun : (fun t => Real.sqrt (‖γ t‖ ^ 2)) = fun t => ‖γ t‖ := by
    funext t
    exact Real.sqrt_sq (norm_nonneg _)
  simp only [hfun] at hroot
  rw [Real.sqrt_sq (norm_nonneg _)] at hroot
  convert hroot using 1
  field_simp
theorem inner_deriv_eq_zero_of_norm_eq_one {σ : ℝ → ℍ[ℝ]} {σ' : ℍ[ℝ]} (hσ : HasDerivAt σ σ' 0)
    (hone : ∀ t, ‖σ t‖ = 1) : inner ℝ (σ 0) σ' = 0 := by
  have hsq : HasDerivAt (fun t => ‖σ t‖ ^ 2) (2 * inner ℝ (σ 0) σ') 0 := hσ.norm_sq
  have hfun : (fun t => ‖σ t‖ ^ 2) = fun _ => (1 : ℝ) := by
    funext t
    rw [hone]
    norm_num
  rw [hfun] at hsq
  have hzero := hsq.unique (hasDerivAt_const 0 (1 : ℝ))
  linarith
theorem exists_hasDerivAt_normalize_le (hγ : HasDerivAt γ γ' 0) (hne : γ 0 ≠ 0) :
    ∃ ν : ℍ[ℝ], HasDerivAt (fun t => ‖γ t‖⁻¹ • γ t) ν 0 ∧ ‖ν‖ ≤ ‖γ'‖ / ‖γ 0‖ := by
  have hn : ‖γ 0‖ ≠ 0 := norm_ne_zero_iff.2 hne
  have hnpos : 0 < ‖γ 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  have hnorm := hasDerivAt_norm_of_ne_zero hγ hne
  have hinv := hnorm.fun_inv hn
  have hprod := hinv.smul hγ
  refine ⟨_, hprod, ?_⟩
  set r := ‖γ 0‖ with hr
  set v : ℍ[ℝ] := r⁻¹ • γ' with hv
  set e : ℍ[ℝ] := r⁻¹ • γ 0 with he
  have he1 : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, Real.norm_of_nonneg hnpos.le, ← hr]
    field_simp
  have hexpr : r⁻¹ • γ' + (-(inner ℝ (γ 0) γ' / r) / r ^ 2) • γ 0 = v - (inner ℝ e v) • e := by
    rw [hv, he, inner_smul_left, inner_smul_right]
    simp only [conj_trivial, smul_smul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    field_simp
  rw [hexpr]
  have hpyth : ‖v - (inner ℝ e v) • e‖ ^ 2 = ‖v‖ ^ 2 - (inner ℝ e v) ^ 2 := by
    have k1 : inner ℝ v ((inner ℝ e v) • e) = (inner ℝ e v) * inner ℝ v e := inner_smul_right _ _ _
    have k2 : ‖(inner ℝ e v) • e‖ = |inner ℝ e v| := by
      rw [norm_smul, he1, mul_one, Real.norm_eq_abs]
    have k3 : inner ℝ v e = inner ℝ e v := real_inner_comm _ _
    rw [norm_sub_sq_real, k1, k2, sq_abs, k3]
    ring
  have hle : ‖v - (inner ℝ e v) • e‖ ≤ ‖v‖ :=
    le_of_not_gt fun hlt => by
      have := pow_lt_pow_left₀ hlt (norm_nonneg v) (by norm_num : (2 : ℕ) ≠ 0)
      nlinarith [sq_nonneg (inner ℝ e v)]
  refine hle.trans (le_of_eq ?_)
  rw [hv, norm_smul, norm_inv, Real.norm_of_nonneg hnpos.le, div_eq_inv_mul]
theorem norm_sum_mul_star_le_of_pure_sum {ι : Type*} (I : Finset ι) (g g' : ι → ℍ[ℝ]) (hg : ∀ i ∈ I, ‖g i‖ = 1)
    (horth : ∀ i ∈ I, inner ℝ (g i) (g' i) = 0) (hpure : pureComponent (∑ i ∈ I, g' i) = 0) {δ : ℝ}
    (hδ : ∀ i ∈ I, ‖g i - 1‖ ≤ δ) : ‖∑ i ∈ I, g' i * star (g i)‖ ≤ δ * ∑ i ∈ I, ‖g' i‖ := by
  have hre : ∀ i ∈ I, (g' i * star (g i)).re = 0 := fun i hi => by
    rw [← inner_eq_re_mul_star]
    exact horth i hi
  have hunit : ∀ i ∈ I, star (g i) * g i = 1 := fun i hi => by
    rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, hg i hi]
    simp
  have hsplit : ∑ i ∈ I, g' i = ∑ i ∈ I, g' i * star (g i) + ∑ i ∈ I, (g' i * star (g i)) * (g i - 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_sub, mul_one, add_sub_cancel, mul_assoc, hunit i hi, mul_one]
  have hfix : pureComponent (∑ i ∈ I, g' i * star (g i)) = ∑ i ∈ I, g' i * star (g i) := by
    refine pureComponent_of_re_eq_zero ?_
    have hsumre : (∑ i ∈ I, g' i * star (g i)).re = ∑ i ∈ I, (g' i * star (g i)).re :=
      map_sum (QuaternionAlgebra.reₗ (-1 : ℝ) (0 : ℝ) (-1 : ℝ)) _ _
    rw [hsumre]
    exact Finset.sum_eq_zero hre
  rw [hsplit, pureComponent_add, hfix] at hpure
  have hsolve : ∑ i ∈ I, g' i * star (g i) = - pureComponent (∑ i ∈ I, (g' i * star (g i)) * (g i - 1)) :=
    eq_neg_of_add_eq_zero_left hpure
  rw [hsolve, norm_neg]
  refine (norm_pureComponent_le _).trans ((norm_sum_le _ _).trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [norm_mul, norm_mul, norm_star, hg i hi, mul_one, mul_comm]
  exact mul_le_mul_of_nonneg_right (hδ i hi) (norm_nonneg _)
theorem norm_sum_deriv_triple_product_le {ι : Type*} (I : Finset ι) (g g' M M' h h' : ι → ℍ[ℝ]) (w : ℍ[ℝ])
    (hw : ‖w‖ = 1) {δ : ℝ}
    (hg : ∀ i ∈ I, ‖g i‖ = 1) (hM : ∀ i ∈ I, ‖M i‖ = 1) (hh : ∀ i ∈ I, ‖h i‖ = 1)
    (hgo : ∀ i ∈ I, inner ℝ (g i) (g' i) = 0) (hho : ∀ i ∈ I, inner ℝ (h i) (h' i) = 0)
    (hgs : pureComponent (∑ i ∈ I, g' i) = 0) (hhs : pureComponent (∑ i ∈ I, h' i) = 0) (hδ0 : 0 ≤ δ)
    (hg1 : ∀ i ∈ I, ‖g i - 1‖ ≤ δ) (hh1 : ∀ i ∈ I, ‖h i - 1‖ ≤ δ)
    (hnear : ∀ i ∈ I, ‖g i * M i * star (h i) - w‖ ≤ δ) :
    ‖∑ i ∈ I, (g' i * M i * star (h i) + g i * M' i * star (h i) + g i * M i * star (h' i))‖ ≤
      ∑ i ∈ I, ‖M' i‖ + 2 * δ * (∑ i ∈ I, ‖g' i‖ + ∑ i ∈ I, ‖h' i‖) := by
  have hgu : ∀ i ∈ I, star (g i) * g i = 1 := fun i hi => by
    rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, hg i hi]
    simp
  have hhu' : ∀ i ∈ I, star (h i) * h i = 1 := fun i hi => by
    rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, hh i hi]
    simp
  set Q : ι → ℍ[ℝ] := fun i => g i * M i * star (h i) with hQ
  have hleft := norm_sum_mul_star_le_of_pure_sum I g g' hg hgo hgs hg1
  have hright := norm_sum_mul_star_le_of_pure_sum I h h' hh hho hhs hh1
  have first : ‖∑ i ∈ I, g' i * M i * star (h i)‖ ≤ 2 * δ * ∑ i ∈ I, ‖g' i‖ := by
    have hexp : ∑ i ∈ I, g' i * M i * star (h i) = (∑ i ∈ I, g' i * star (g i)) * w +
        ∑ i ∈ I, (g' i * star (g i)) * (Q i - w) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have : g' i * M i * star (h i) = (g' i * star (g i)) * Q i := by
        simp only [hQ]
        calc g' i * M i * star (h i) = g' i * (star (g i) * g i) * M i * star (h i) := by rw [hgu i hi, mul_one]
          _ = _ := by simp only [mul_assoc]
      rw [this]
      noncomm_ring
    rw [hexp]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hw, mul_one]
    have hrest : ‖∑ i ∈ I, (g' i * star (g i)) * (Q i - w)‖ ≤ δ * ∑ i ∈ I, ‖g' i‖ := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [norm_mul, norm_mul, norm_star, hg i hi, mul_one, mul_comm]
      exact mul_le_mul_of_nonneg_right (hnear i hi) (norm_nonneg _)
    linarith
  have third : ‖∑ i ∈ I, g i * M i * star (h' i)‖ ≤ 2 * δ * ∑ i ∈ I, ‖h' i‖ := by
    have hexp : ∑ i ∈ I, g i * M i * star (h' i) = w * star (∑ i ∈ I, h' i * star (h i)) +
        ∑ i ∈ I, (Q i - w) * star (h' i * star (h i)) := by
      rw [star_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have : g i * M i * star (h' i) = Q i * star (h' i * star (h i)) := by
        simp only [hQ, star_mul, star_star]
        calc g i * M i * star (h' i) = g i * M i * (star (h i) * h i) * star (h' i) := by rw [hhu' i hi, mul_one]
          _ = _ := by simp only [mul_assoc]
      rw [this]
      noncomm_ring
    rw [hexp]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hw, one_mul, norm_star]
    have hrest : ‖∑ i ∈ I, (Q i - w) * star (h' i * star (h i))‖ ≤ δ * ∑ i ∈ I, ‖h' i‖ := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [norm_mul, norm_star, norm_mul, norm_star, hh i hi, mul_one]
      exact mul_le_mul_of_nonneg_right (hnear i hi) (norm_nonneg _)
    linarith
  have second : ‖∑ i ∈ I, g i * M' i * star (h i)‖ ≤ ∑ i ∈ I, ‖M' i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, norm_mul, norm_star, hg i hi, hh i hi]
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le (∑ i ∈ I, g' i * M i * star (h i)) (∑ i ∈ I, g i * M' i * star (h i))
  linarith
theorem abs_inner_sum_deriv_le {ι : Type*} (I : Finset ι) (σ σ' : ι → ℍ[ℝ]) (w : ℍ[ℝ]) {δ : ℝ}
    (horth : ∀ i ∈ I, inner ℝ (σ i) (σ' i) = 0)
    (hw : ∀ i ∈ I, ‖w - σ i‖ ≤ δ) : |inner ℝ w (∑ i ∈ I, σ' i)| ≤ δ * ∑ i ∈ I, ‖σ' i‖ := by
  rw [inner_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hshift : inner ℝ w (σ' i) = inner ℝ (w - σ i) (σ' i) := by
    rw [inner_sub_left, horth i hi, sub_zero]
  rw [hshift]
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (hw i hi) (norm_nonneg _)
end UnitCurves
end YangMills.Construction
end
