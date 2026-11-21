import YangMills.Construction.Coercivity.FiniteFamilyBounds
import YangMills.Construction.SpectralTheory.UnboundedBorelCalculusFromTruncations
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Coercivity
section Sums
variable {κ : Type}
theorem norm_sum_mul_sq_le_sum_mul_sum (s : Finset κ) (a b : κ → ℂ) :
    ‖∑ m ∈ s, a m * b m‖ ^ 2 ≤ (∑ m ∈ s, ‖a m‖ ^ 2) * ∑ m ∈ s, ‖b m‖ ^ 2 := by
  have h1 : ‖∑ m ∈ s, a m * b m‖ ≤ ∑ m ∈ s, ‖a m‖ * ‖b m‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun m _ => norm_mul _ _
  calc ‖∑ m ∈ s, a m * b m‖ ^ 2 ≤ (∑ m ∈ s, ‖a m‖ * ‖b m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
theorem sq_norm_add_mul_expand (e d t : ℂ) :
    ‖e + d * t‖ ^ 2 = ‖e‖ ^ 2 + ‖d‖ ^ 2 * ‖t‖ ^ 2 + 2 * (conj t * (conj d * e)).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring
theorem sum_sq_norm_add_mul_of_orthogonal (s : Finset κ) (d e : κ → ℂ) (t : ℂ)
    (h : ∑ m ∈ s, conj (d m) * e m = 0) :
    ∑ m ∈ s, ‖e m + d m * t‖ ^ 2 = ∑ m ∈ s, ‖e m‖ ^ 2 + (∑ m ∈ s, ‖d m‖ ^ 2) * ‖t‖ ^ 2 := by
  have h0 : ∑ m ∈ s, (conj t * (conj (d m) * e m)).re = 0 := by
    rw [← Complex.re_sum, ← Finset.mul_sum, h]
    simp
  simp only [sq_norm_add_mul_expand, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h0]
  ring
theorem sq_norm_add_le_two_mul (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
theorem sq_norm_sub_le_two_mul (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by apply _root_.YangMills.Construction.BorelCalculus.Unbounded.norm_sub_sq_le_two_mul <;> assumption
theorem sq_norm_real_eq (x : ℝ) : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
theorem sq_norm_weighted_sum_le (s : Finset κ) (v : κ → ℝ) (l : κ → ℂ) :
    ‖∑ m ∈ s, (v m : ℂ) * l m‖ ^ 2 ≤ (∑ m ∈ s, v m ^ 2) * ∑ m ∈ s, ‖l m‖ ^ 2 := by
  have h := norm_sum_mul_sq_le_sum_mul_sum s (fun m => (v m : ℂ)) l
  simpa only [sq_norm_real_eq] using h
theorem sum_mul_sub_weightedSiteSum_eq_zero {s : Finset κ} {v : κ → ℝ}
    (hs : ∑ m ∈ s, v m ^ 2 = 1) (χ : κ → ℂ) :
    ∑ m ∈ s, (v m : ℂ) * (χ m - v m * weightedSiteSum s v χ) = 0 := by
  have h : ∑ m ∈ s, (v m : ℂ) * ((v m : ℂ) * weightedSiteSum s v χ) = weightedSiteSum s v χ := by
    have h1 : ∑ m ∈ s, (v m : ℂ) ^ 2 = 1 := by exact_mod_cast hs
    calc ∑ m ∈ s, (v m : ℂ) * ((v m : ℂ) * weightedSiteSum s v χ)
        = (∑ m ∈ s, (v m : ℂ) ^ 2) * weightedSiteSum s v χ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun m _ => by ring
      _ = weightedSiteSum s v χ := by rw [h1, one_mul]
  calc ∑ m ∈ s, (v m : ℂ) * (χ m - v m * weightedSiteSum s v χ)
      = ∑ m ∈ s, (v m : ℂ) * χ m -
          ∑ m ∈ s, (v m : ℂ) * ((v m : ℂ) * weightedSiteSum s v χ) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
    _ = 0 := by
        rw [h]
        exact sub_self _
theorem sum_sq_norm_eq_rest_add_mean {s : Finset κ} {v : κ → ℝ} (hs : ∑ m ∈ s, v m ^ 2 = 1)
    (χ : κ → ℂ) :
    ∑ m ∈ s, ‖χ m‖ ^ 2 =
      ∑ m ∈ s, ‖χ m - v m * weightedSiteSum s v χ‖ ^ 2 + ‖weightedSiteSum s v χ‖ ^ 2 := by
  have h := sum_sq_norm_add_mul_of_orthogonal s (fun m => (v m : ℂ))
    (fun m => χ m - v m * weightedSiteSum s v χ) (weightedSiteSum s v χ)
    (by simpa only [Complex.conj_ofReal] using sum_mul_sub_weightedSiteSum_eq_zero hs χ)
  simp only [sub_add_cancel, sq_norm_real_eq, hs, one_mul] at h
  exact h
end Sums
section Family
variable {ι : Type} [DecidableEq ι] {p r B T : ℝ} {s : Finset ι} {z : ι} {D : ι → ℝ}
  {d : ι → Fin 4 → ℂ} {v : ι → ℝ} {u : ι → Fin 4 → ℂ} {dc : Fin 4 → ℂ}
theorem IsAdmissibleFamily.weight_nonneg (hf : IsAdmissibleFamily p r B T s z D d v u dc)
    {m : ι} (hm : m ∈ s) : 0 ≤ D m := by
  rw [hf.eq_normSq m hm]
  exact Finset.sum_nonneg fun μ _ => by positivity
theorem IsAdmissibleFamily.site_sq_split (hf : IsAdmissibleFamily p r B T s z D d v u dc) :
    v z ^ 2 + ∑ m ∈ s.erase z, v m ^ 2 = 1 := by
  rw [Finset.add_sum_erase s (fun m => v m ^ 2) hf.mem]
  exact hf.site_sum_sq
theorem IsAdmissibleFamily.site_sq_le_one (hf : IsAdmissibleFamily p r B T s z D d v u dc) :
    v z ^ 2 ≤ 1 := by
  have h1 := hf.site_sq_split
  have h : 0 ≤ ∑ m ∈ s.erase z, v m ^ 2 := Finset.sum_nonneg fun m _ => sq_nonneg _
  linarith
theorem bondSobolevSq_eq (s : Finset ι) (D : ι → ℝ) (b : ι → Fin 4 → ℂ) :
    bondSobolevSq s D b = bondDirichlet s D b + ∑ m ∈ s, bondNormSq b m := by
  simp only [bondSobolevSq, bondDirichlet, add_mul, one_mul, Finset.sum_add_distrib]
theorem siteSobolevSq_eq (s : Finset ι) (D : ι → ℝ) (l : ι → ℂ) :
    siteSobolevSq s D l = siteDirichlet s D l + ∑ m ∈ s, ‖l m‖ ^ 2 := by
  simp only [siteSobolevSq, siteDirichlet, add_mul, one_mul, Finset.sum_add_distrib]
theorem siteQuadraticForm_le (hf : IsAdmissibleFamily p r B T s z D d v u dc) (l : ι → ℂ) :
    siteQuadraticForm s D v l ≤ siteSobolevSq s D l := by
  have h := sq_norm_weighted_sum_le s v l
  rw [hf.site_sum_sq, one_mul] at h
  rw [siteSobolevSq_eq]
  simp only [siteQuadraticForm, weightedSiteSum]
  linarith
theorem bondQuadraticForm_le (hf : IsAdmissibleFamily p r B T s z D d v u dc)
    (b : ι → Fin 4 → ℂ) : bondQuadraticForm s D d v u b ≤ bondSobolevSq s D b := by
  have h : ∑ μ, ‖weightedBondSum s u b μ‖ ^ 2 ≤ ∑ m ∈ s, bondNormSq b m := by
    simp only [bondNormSq]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun μ _ => ?_
    have h1 := norm_sum_mul_sq_le_sum_mul_sum s (fun m => u m μ) (fun m => b m μ)
    have h2 : 0 ≤ ∑ m ∈ s, ‖b m μ‖ ^ 2 := Finset.sum_nonneg fun m _ => by positivity
    exact h1.trans (mul_le_of_le_one_left h2 (hf.bond_sum_sq_le μ))
  rw [bondSobolevSq_eq]
  simp only [bondQuadraticForm]
  nlinarith [sq_nonneg ‖weightedSiteSum s v (familyDivergence d b)‖]
theorem le_siteQuadraticForm (hp : 0 < p) (hf : IsAdmissibleFamily p r B T s z D d v u dc)
    (l : ι → ℂ) :
    min (p ^ 2 / 2) (3 / 5) * siteSobolevSq s D l ≤ siteQuadraticForm s D v l := by
  obtain ⟨c, hc⟩ : ∃ c, c = min (p ^ 2 / 2) (3 / 5) := ⟨_, rfl⟩
  rw [← hc]
  have hc1 : c ≤ p ^ 2 / 2 := hc ▸ min_le_left _ _
  have hc2 : c ≤ 3 / 5 := hc ▸ min_le_right _ _
  have hc0 : 0 < c := by
    rw [hc]
    exact lt_min (by positivity) (by norm_num)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ m ∈ s.erase z, D m * ‖l m‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = ∑ m ∈ s.erase z, ‖l m‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = ‖weightedSiteSum s v l‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = ‖l z‖ ^ 2 := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by
    rw [hx]
    positivity
  have hLQ : 4 * L ≤ Q := by
    rw [hL, hQ, Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    exact mul_le_mul_of_nonneg_right
      (hf.four_le m (Finset.mem_of_mem_erase hm) (Finset.ne_of_mem_erase hm)) (by positivity)
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Finset.sum_nonneg fun m _ => by positivity
  have hE : siteDirichlet s D l = D z * x + Q := by
    rw [hx, hQ]
    simp only [siteDirichlet]
    exact (Finset.add_sum_erase s (fun m => D m * ‖l m‖ ^ 2) hf.mem).symm
  have hS : ∑ m ∈ s, ‖l m‖ ^ 2 = x + L := by
    rw [hx, hL]
    exact (Finset.add_sum_erase s (fun m => ‖l m‖ ^ 2) hf.mem).symm
  have hy : ‖∑ m ∈ s.erase z, (v m : ℂ) * l m‖ ^ 2 ≤ L := by
    have h1 := sq_norm_weighted_sum_le (s.erase z) v l
    rw [← hL] at h1
    have h2 : ∑ m ∈ s.erase z, v m ^ 2 ≤ 1 := by
      have := hf.site_sq_split
      nlinarith [sq_nonneg (v z)]
    exact h1.trans (mul_le_of_le_one_left hL0 h2)
  have hzm : (v z : ℂ) * l z = weightedSiteSum s v l - ∑ m ∈ s.erase z, (v m : ℂ) * l m := by
    simp only [weightedSiteSum]
    rw [← Finset.add_sum_erase s _ hf.mem]
    ring
  have hz : v z ^ 2 * x ≤ 2 * M + 2 * L := by
    have h1 := sq_norm_sub_le_two_mul (weightedSiteSum s v l) (∑ m ∈ s.erase z, (v m : ℂ) * l m)
    rw [← hzm, norm_mul, mul_pow, sq_norm_real_eq, ← hx, ← hM] at h1
    linarith
  have hp2 : p ^ 2 ≤ v z ^ 2 := pow_le_pow_left₀ hp.le hf.site_lower 2
  have hD0 : 0 ≤ D z := hf.weight_nonneg hf.mem
  have hN : siteSobolevSq s D l = D z * x + Q + (x + L) := by
    rw [siteSobolevSq_eq, hE, hS]
  have hF : siteQuadraticForm s D v l = D z * x + Q + M := by
    simp only [siteQuadraticForm]
    rw [hE, hM]
  rw [hN, hF]
  have h1 : c * (D z * x) ≤ D z * x :=
    mul_le_of_le_one_left (mul_nonneg hD0 hx0) (by linarith)
  have h2 : c * x ≤ p ^ 2 / 2 * x := mul_le_mul_of_nonneg_right hc1 hx0
  have h3 : p ^ 2 * x ≤ v z ^ 2 * x := mul_le_mul_of_nonneg_right hp2 hx0
  have h4 : c * (Q + L) ≤ 3 / 5 * (Q + L) :=
    mul_le_mul_of_nonneg_right hc2 (by linarith)
  nlinarith
theorem sq_div_le_sq_mul_inv {a x Dz : ℝ} (ha : 0 ≤ a) (hx : a ≤ x) (hD : 0 ≤ Dz) (hB : Dz ≤ B) :
    a ^ 2 / (B + 1) ≤ x ^ 2 * (Dz + 1)⁻¹ := by
  rw [div_eq_mul_inv]
  exact mul_le_mul (pow_le_pow_left₀ ha hx 2) (inv_anti₀ (by linarith) (by linarith))
    (inv_nonneg.2 (by linarith)) (by positivity)
theorem le_bondResolventWeight (hr : 0 < r) (hf : IsAdmissibleFamily p r B T s z D d v u dc)
    (μ : Fin 4) : min (r ^ 2) (p ^ 2) / (B + 1) ≤ bondResolventWeight s D u μ := by
  have hD0 := hf.weight_nonneg hf.mem
  have hB1 : 0 < B + 1 := by linarith [hf.le_bound]
  have h1 : r ^ 2 / (B + 1) ≤ ‖u z μ‖ ^ 2 * (D z + 1)⁻¹ :=
    sq_div_le_sq_mul_inv hr.le (hf.bond_lower μ) hD0 hf.le_bound
  have h2 : ‖u z μ‖ ^ 2 * (D z + 1)⁻¹ ≤ bondResolventWeight s D u μ := by
    refine Finset.single_le_sum (f := fun m => ‖u m μ‖ ^ 2 * (D m + 1)⁻¹) (fun m hm => ?_) hf.mem
    have := hf.weight_nonneg hm
    positivity
  exact (div_le_div_of_nonneg_right (min_le_left _ _) hB1.le).trans (h1.trans h2)
theorem le_siteResolventWeight (hp : 0 < p) (hf : IsAdmissibleFamily p r B T s z D d v u dc) :
    min (r ^ 2) (p ^ 2) / (B + 1) ≤ siteResolventWeight s D v := by
  have hD0 := hf.weight_nonneg hf.mem
  have hB1 : 0 < B + 1 := by linarith [hf.le_bound]
  have h1 : p ^ 2 / (B + 1) ≤ v z ^ 2 * (D z + 1)⁻¹ :=
    sq_div_le_sq_mul_inv hp.le hf.site_lower hD0 hf.le_bound
  have h2 : v z ^ 2 * (D z + 1)⁻¹ ≤ siteResolventWeight s D v := by
    refine Finset.single_le_sum (f := fun m => v m ^ 2 * (D m + 1)⁻¹) (fun m hm => ?_) hf.mem
    have := hf.weight_nonneg hm
    positivity
  exact (div_le_div_of_nonneg_right (min_le_right _ _) hB1.le).trans (h1.trans h2)
def normalCoeff (D : ι → ℝ) (d b : ι → Fin 4 → ℂ) (m : ι) : ℂ :=
  familyDivergence d b m / (D m : ℂ)
def tangentPart (D : ι → ℝ) (d b : ι → Fin 4 → ℂ) (m : ι) (μ : Fin 4) : ℂ :=
  b m μ - d m μ * normalCoeff D d b m
theorem sum_conj_mul_self_eq_weight (hf : IsAdmissibleFamily p r B T s z D d v u dc) {m : ι}
    (hm : m ∈ s) : ∑ μ, conj (d m μ) * d m μ = (D m : ℂ) := by
  rw [hf.eq_normSq m hm]
  push_cast
  exact Finset.sum_congr rfl fun μ _ => Complex.conj_mul' _
theorem weight_mul_normalCoeff (hf : IsAdmissibleFamily p r B T s z D d v u dc) {m : ι}
    (hm : m ∈ s) (b : ι → Fin 4 → ℂ) :
    (D m : ℂ) * normalCoeff D d b m = familyDivergence d b m := by
  by_cases h : D m = 0
  · have hd : ∀ μ, d m μ = 0 := by
      intro μ
      have h1 := hf.eq_normSq m hm
      rw [h] at h1
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun μ _ => by positivity)).1 h1.symm μ (Finset.mem_univ _)
      simpa using h2
    simp [normalCoeff, familyDivergence, h, hd]
  · have h' : (D m : ℂ) ≠ 0 := by exact_mod_cast h
    simp only [normalCoeff]
    field_simp
theorem sum_conj_mul_tangentPart (hf : IsAdmissibleFamily p r B T s z D d v u dc) {m : ι}
    (hm : m ∈ s) (b : ι → Fin 4 → ℂ) : ∑ μ, conj (d m μ) * tangentPart D d b m μ = 0 := by
  have h : ∀ μ, conj (d m μ) * tangentPart D d b m μ =
      conj (d m μ) * b m μ - conj (d m μ) * d m μ * normalCoeff D d b m := by
    intro μ
    simp only [tangentPart]
    ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_conj_mul_self_eq_weight hf hm, weight_mul_normalCoeff hf hm]
  exact sub_self _
theorem bondNormSq_split (hf : IsAdmissibleFamily p r B T s z D d v u dc) {m : ι} (hm : m ∈ s)
    (b : ι → Fin 4 → ℂ) :
    bondNormSq b m = bondNormSq (tangentPart D d b) m + D m * ‖normalCoeff D d b m‖ ^ 2 := by
  have h := sum_sq_norm_add_mul_of_orthogonal Finset.univ (d m) (tangentPart D d b m)
    (normalCoeff D d b m) (sum_conj_mul_tangentPart hf hm b)
  rw [← hf.eq_normSq m hm] at h
  have e : ∀ μ, tangentPart D d b m μ + d m μ * normalCoeff D d b m = b m μ := fun μ => by
    simp [tangentPart]
  simp only [e] at h
  exact h
theorem sq_norm_familyDivergence_eq (hf : IsAdmissibleFamily p r B T s z D d v u dc) {m : ι}
    (hm : m ∈ s) (b : ι → Fin 4 → ℂ) :
    ‖familyDivergence d b m‖ ^ 2 = D m ^ 2 * ‖normalCoeff D d b m‖ ^ 2 := by
  rw [← weight_mul_normalCoeff hf hm b, norm_mul, mul_pow, sq_norm_real_eq]
theorem weight_mul_bondNormSq_split (hf : IsAdmissibleFamily p r B T s z D d v u dc) {m : ι}
    (hm : m ∈ s) (b : ι → Fin 4 → ℂ) :
    D m * bondNormSq b m = D m * bondNormSq (tangentPart D d b) m + ‖familyDivergence d b m‖ ^ 2 := by
  rw [sq_norm_familyDivergence_eq hf hm b, bondNormSq_split hf hm b]
  ring
theorem tangentPart_at_base_bound (hp : 0 < p) (hr : 0 < r)
    (hf : IsAdmissibleFamily p r B T s z D d v u dc) (b : ι → Fin 4 → ℂ) :
    r ^ 2 * (bondNormSq (tangentPart D d b) z +
        D z * ‖(∑ m ∈ s, (v m : ℂ) * normalCoeff D d b m) / (v z : ℂ)‖ ^ 2) ≤
      2 * ∑ μ, ‖weightedBondSum s u b μ‖ ^ 2 +
        2 * ∑ m ∈ s.erase z, bondNormSq (tangentPart D d b) m := by
  obtain ⟨β, hβ⟩ : ∃ β, β = ∑ m ∈ s, (v m : ℂ) * normalCoeff D d b m := ⟨_, rfl⟩
  rw [← hβ]
  obtain ⟨t, ht⟩ : ∃ t, t = β / (v z : ℂ) := ⟨_, rfl⟩
  rw [← ht]
  have hv : (v z : ℂ) ≠ 0 := by
    have : v z ≠ 0 := (lt_of_lt_of_le hp hf.site_lower).ne'
    exact_mod_cast this
  have hβt : β = v z * t := by
    rw [ht]
    field_simp
  have key : ∀ μ, r ^ 2 * ‖tangentPart D d b z μ + d z μ * t‖ ^ 2 ≤
      2 * ‖weightedBondSum s u b μ‖ ^ 2 + 2 * ∑ m ∈ s.erase z, ‖tangentPart D d b m μ‖ ^ 2 := by
    intro μ
    have e2 : ∀ m ∈ s, u m μ * b m μ =
        u m μ * tangentPart D d b m μ + dc μ * ((v m : ℂ) * normalCoeff D d b m) := by
      intro m hm
      have h := hf.mul_eq m hm μ
      calc u m μ * b m μ =
            u m μ * tangentPart D d b m μ + (u m μ * d m μ) * normalCoeff D d b m := by
            simp only [tangentPart]
            ring
        _ = _ := by
            rw [h]
            ring
    have e3 : weightedBondSum s u b μ = ∑ m ∈ s, u m μ * tangentPart D d b m μ + dc μ * β := by
      simp only [weightedBondSum]
      rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib, ← Finset.mul_sum, hβ]
    have e4 : u z μ * (tangentPart D d b z μ + d z μ * t) =
        weightedBondSum s u b μ - ∑ m ∈ s.erase z, u m μ * tangentPart D d b m μ := by
      rw [e3, ← Finset.add_sum_erase s (fun m => u m μ * tangentPart D d b m μ) hf.mem, hβt]
      have h := hf.mul_eq z hf.mem μ
      linear_combination t * h
    have hu : r ^ 2 ≤ ‖u z μ‖ ^ 2 := pow_le_pow_left₀ hr.le (hf.bond_lower μ) 2
    have h1 : ‖u z μ‖ ^ 2 * ‖tangentPart D d b z μ + d z μ * t‖ ^ 2 =
        ‖weightedBondSum s u b μ - ∑ m ∈ s.erase z, u m μ * tangentPart D d b m μ‖ ^ 2 := by
      rw [← e4, norm_mul, mul_pow]
    have h2 := sq_norm_sub_le_two_mul (weightedBondSum s u b μ)
      (∑ m ∈ s.erase z, u m μ * tangentPart D d b m μ)
    have h3 : ‖∑ m ∈ s.erase z, u m μ * tangentPart D d b m μ‖ ^ 2 ≤
        ∑ m ∈ s.erase z, ‖tangentPart D d b m μ‖ ^ 2 := by
      have h4 := norm_sum_mul_sq_le_sum_mul_sum (s.erase z) (fun m => u m μ)
        (fun m => tangentPart D d b m μ)
      have h5 : ∑ m ∈ s.erase z, ‖u m μ‖ ^ 2 ≤ 1 :=
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by positivity)).trans (hf.bond_sum_sq_le μ)
      exact h4.trans (mul_le_of_le_one_left
        (Finset.sum_nonneg fun m _ => by positivity) h5)
    have h6 : r ^ 2 * ‖tangentPart D d b z μ + d z μ * t‖ ^ 2 ≤
        ‖u z μ‖ ^ 2 * ‖tangentPart D d b z μ + d z μ * t‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hu (by positivity)
    linarith
  have hw : ∑ μ, ‖tangentPart D d b z μ + d z μ * t‖ ^ 2 =
      bondNormSq (tangentPart D d b) z + D z * ‖t‖ ^ 2 := by
    have h := sum_sq_norm_add_mul_of_orthogonal Finset.univ (d z) (tangentPart D d b z) t
      (sum_conj_mul_tangentPart hf hf.mem b)
    rw [← hf.eq_normSq z hf.mem] at h
    exact h
  calc r ^ 2 * (bondNormSq (tangentPart D d b) z + D z * ‖t‖ ^ 2)
      = ∑ μ, r ^ 2 * ‖tangentPart D d b z μ + d z μ * t‖ ^ 2 := by rw [← hw, Finset.mul_sum]
    _ ≤ ∑ μ, (2 * ‖weightedBondSum s u b μ‖ ^ 2 +
          2 * ∑ m ∈ s.erase z, ‖tangentPart D d b m μ‖ ^ 2) :=
        Finset.sum_le_sum fun μ _ => key μ
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
        simp only [bondNormSq]
theorem sq_norm_weighted_rest_le (hf : IsAdmissibleFamily p r B T s z D d v u dc) (hD : 0 < D z)
    (ρ : ι → ℂ) (h0 : ∑ m ∈ s, (v m : ℂ) * ρ m = 0) :
    D z * ‖∑ m ∈ s, (v m : ℂ) * (ρ m / (D m : ℂ))‖ ^ 2 ≤
      T * (1 + B / 4) ^ 2 * ∑ m ∈ s, ‖ρ m‖ ^ 2 := by
  have hB : 0 < B := lt_of_lt_of_le hD hf.le_bound
  have hW : ∑ m ∈ s, (v m : ℂ) * (ρ m / (D m : ℂ)) =
      ∑ m ∈ s.erase z, (v m : ℂ) * (ρ m * (((D m)⁻¹ - (D z)⁻¹ : ℝ) : ℂ)) := by
    have e : ∑ m ∈ s, (v m : ℂ) * (ρ m * (((D m)⁻¹ - (D z)⁻¹ : ℝ) : ℂ)) =
        ∑ m ∈ s, (v m : ℂ) * (ρ m / (D m : ℂ)) - (D z : ℂ)⁻¹ * ∑ m ∈ s, (v m : ℂ) * ρ m := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast
      ring
    rw [h0, mul_zero, sub_zero] at e
    rw [← e, ← Finset.add_sum_erase s
      (fun m => (v m : ℂ) * (ρ m * (((D m)⁻¹ - (D z)⁻¹ : ℝ) : ℂ))) hf.mem]
    simp
  rw [hW]
  have hcs := norm_sum_mul_sq_le_sum_mul_sum (s.erase z) (fun m => (v m : ℂ))
    (fun m => ρ m * (((D m)⁻¹ - (D z)⁻¹ : ℝ) : ℂ))
  have hv : ∑ m ∈ s.erase z, ‖(v m : ℂ)‖ ^ 2 = 1 - v z ^ 2 := by
    simp only [sq_norm_real_eq]
    linarith [hf.site_sq_split]
  rw [hv] at hcs
  have hw : ∀ m ∈ s.erase z, D z ^ 2 * ‖ρ m * (((D m)⁻¹ - (D z)⁻¹ : ℝ) : ℂ)‖ ^ 2 ≤
      (1 + B / 4) ^ 2 * ‖ρ m‖ ^ 2 := by
    intro m hm
    have h4 := hf.four_le m (Finset.mem_of_mem_erase hm) (Finset.ne_of_mem_erase hm)
    have hDm : 0 < D m := by linarith
    rw [norm_mul, mul_pow, sq_norm_real_eq]
    have hx : (D z * ((D m)⁻¹ - (D z)⁻¹)) ^ 2 ≤ (1 + B / 4) ^ 2 := by
      have e : D z * ((D m)⁻¹ - (D z)⁻¹) = D z * (D m)⁻¹ - 1 := by
        field_simp
      have h5 : D z * (D m)⁻¹ ≤ B * 4⁻¹ :=
        mul_le_mul hf.le_bound (inv_anti₀ (by norm_num) h4) (by positivity) hB.le
      have h6 : 0 ≤ D z * (D m)⁻¹ := by positivity
      rw [e]
      apply sq_le_sq' <;> linarith
    calc D z ^ 2 * (‖ρ m‖ ^ 2 * ((D m)⁻¹ - (D z)⁻¹) ^ 2)
        = (D z * ((D m)⁻¹ - (D z)⁻¹)) ^ 2 * ‖ρ m‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hx (by positivity)
  have hsum : D z ^ 2 * ∑ m ∈ s.erase z, ‖ρ m * (((D m)⁻¹ - (D z)⁻¹ : ℝ) : ℂ)‖ ^ 2 ≤
      (1 + B / 4) ^ 2 * ∑ m ∈ s, ‖ρ m‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hw).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset _ _) (fun _ _ _ => by positivity)) (by positivity)
  have hdef : 0 ≤ 1 - v z ^ 2 := by linarith [hf.site_sq_le_one]
  obtain ⟨W, hWd⟩ : ∃ W, W = ‖∑ m ∈ s.erase z, (v m : ℂ) *
      (ρ m * (((D m)⁻¹ - (D z)⁻¹ : ℝ) : ℂ))‖ ^ 2 := ⟨_, rfl⟩
  rw [← hWd] at hcs ⊢
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ m ∈ s, ‖ρ m‖ ^ 2 := ⟨_, rfl⟩
  rw [← hR] at hsum ⊢
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact Finset.sum_nonneg fun m _ => by positivity
  have h1 : D z ^ 2 * W ≤ (1 - v z ^ 2) * ((1 + B / 4) ^ 2 * R) :=
    calc D z ^ 2 * W ≤ D z ^ 2 * ((1 - v z ^ 2) *
          ∑ m ∈ s.erase z, ‖ρ m * (((D m)⁻¹ - (D z)⁻¹ : ℝ) : ℂ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (1 - v z ^ 2) * (D z ^ 2 *
          ∑ m ∈ s.erase z, ‖ρ m * (((D m)⁻¹ - (D z)⁻¹ : ℝ) : ℂ)‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hdef
  have h2 : (1 - v z ^ 2) * ((1 + B / 4) ^ 2 * R) ≤ T * D z * ((1 + B / 4) ^ 2 * R) :=
    mul_le_mul_of_nonneg_right (by linarith [hf.deficit_le]) (by positivity)
  refine le_of_mul_le_mul_left ?_ hD
  calc D z * (D z * W) = D z ^ 2 * W := by ring
    _ ≤ T * D z * ((1 + B / 4) ^ 2 * R) := h1.trans h2
    _ = D z * (T * (1 + B / 4) ^ 2 * R) := by ring
theorem sq_norm_weightedSiteSum_le (hp : 0 < p) (hf : IsAdmissibleFamily p r B T s z D d v u dc)
    (hD : 0 < D z) (χ : ι → ℂ) :
    p ^ 4 * ‖weightedSiteSum s v χ‖ ^ 2 ≤
      2 * D z * (D z * ‖∑ m ∈ s, (v m : ℂ) * (χ m / (D m : ℂ))‖ ^ 2 +
        T * (1 + B / 4) ^ 2 * ∑ m ∈ s, ‖χ m - v m * weightedSiteSum s v χ‖ ^ 2) := by
  have hWb := sq_norm_weighted_rest_le hf hD (fun m => χ m - v m * weightedSiteSum s v χ)
    (sum_mul_sub_weightedSiteSum_eq_zero hf.site_sum_sq χ)
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = weightedSiteSum s v χ := ⟨_, rfl⟩
  rw [← hγ] at hWb ⊢
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ m ∈ s, (v m : ℂ) * ((χ m - v m * γ) / (D m : ℂ)) := ⟨_, rfl⟩
  rw [← hW] at hWb
  obtain ⟨β, hβ⟩ : ∃ β, β = ∑ m ∈ s, (v m : ℂ) * (χ m / (D m : ℂ)) := ⟨_, rfl⟩
  rw [← hβ]
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ m ∈ s, v m ^ 2 * (D m)⁻¹ := ⟨_, rfl⟩
  have hsplit : β = W + (S : ℂ) * γ := by
    rw [hβ, hW, hS]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hDS : p ^ 2 ≤ D z * S := by
    have h1 : v z ^ 2 * (D z)⁻¹ ≤ S := by
      rw [hS]
      exact Finset.single_le_sum (f := fun m => v m ^ 2 * (D m)⁻¹)
        (fun m hm => mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hf.weight_nonneg hm))) hf.mem
    have h2 : D z * (v z ^ 2 * (D z)⁻¹) = v z ^ 2 := by
      field_simp
    have h3 : p ^ 2 ≤ v z ^ 2 := pow_le_pow_left₀ hp.le hf.site_lower 2
    have h4 : D z * (v z ^ 2 * (D z)⁻¹) ≤ D z * S := mul_le_mul_of_nonneg_left h1 hD.le
    linarith
  have h1 : S ^ 2 * ‖γ‖ ^ 2 ≤ 2 * ‖β‖ ^ 2 + 2 * ‖W‖ ^ 2 := by
    have e : (S : ℂ) * γ = β - W := by
      rw [hsplit]
      ring
    have h := sq_norm_sub_le_two_mul β W
    rw [← e, norm_mul, mul_pow, sq_norm_real_eq] at h
    exact h
  have h2 : (p ^ 2) ^ 2 ≤ (D z * S) ^ 2 := pow_le_pow_left₀ (by positivity) hDS 2
  have h3 : p ^ 4 * ‖γ‖ ^ 2 ≤ (D z * S) ^ 2 * ‖γ‖ ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc p ^ 4 = (p ^ 2) ^ 2 := by ring
      _ ≤ _ := h2
  have h4 : D z ^ 2 * (S ^ 2 * ‖γ‖ ^ 2) ≤ D z ^ 2 * (2 * ‖β‖ ^ 2 + 2 * ‖W‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h5 : 2 * D z * (D z * ‖W‖ ^ 2) ≤ 2 * D z *
      (T * (1 + B / 4) ^ 2 * ∑ m ∈ s, ‖χ m - v m * γ‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hWb (by positivity)
  nlinarith
theorem rest_at_base_le (hf : IsAdmissibleFamily p r B T s z D d v u dc) (ρ : ι → ℂ)
    (h0 : ∑ m ∈ s, (v m : ℂ) * ρ m = 0) :
    v z ^ 2 * ‖ρ z‖ ^ 2 ≤ (1 - v z ^ 2) * ∑ m ∈ s, ‖ρ m‖ ^ 2 := by
  have e : (v z : ℂ) * ρ z = -∑ m ∈ s.erase z, (v m : ℂ) * ρ m := by
    rw [← Finset.add_sum_erase s (fun m => (v m : ℂ) * ρ m) hf.mem] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have h1 := sq_norm_weighted_sum_le (s.erase z) v ρ
  have h2 : ‖(v z : ℂ) * ρ z‖ ^ 2 = v z ^ 2 * ‖ρ z‖ ^ 2 := by
    rw [norm_mul, mul_pow, sq_norm_real_eq]
  rw [← h2, e, norm_neg]
  refine h1.trans ?_
  have h3 : ∑ m ∈ s.erase z, v m ^ 2 = 1 - v z ^ 2 := by linarith [hf.site_sq_split]
  rw [h3]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.erase_subset _ _) (fun _ _ _ => by positivity)) (by linarith [hf.site_sq_le_one])
theorem sq_norm_weightedSiteSum_nonpos_of_weight_eq_zero
    (hf : IsAdmissibleFamily p r B T s z D d v u dc) (h0 : D z = 0) (χ : ι → ℂ)
    (hχ : χ z = 0) : ‖weightedSiteSum s v χ‖ ^ 2 ≤ 0 := by
  have h1 : ∑ m ∈ s.erase z, v m ^ 2 ≤ 0 := by
    have h2 := hf.deficit_le
    rw [h0, mul_zero] at h2
    linarith [hf.site_sq_split]
  have e : weightedSiteSum s v χ = ∑ m ∈ s.erase z, (v m : ℂ) * χ m := by
    simp only [weightedSiteSum]
    rw [← Finset.add_sum_erase s (fun m => (v m : ℂ) * χ m) hf.mem, hχ]
    simp
  rw [e]
  refine (sq_norm_weighted_sum_le (s.erase z) v χ).trans ?_
  exact mul_nonpos_of_nonpos_of_nonneg h1 (Finset.sum_nonneg fun m _ => by positivity)
def tangentConstant (r : ℝ) : ℝ := 2 / r ^ 2
def meanConstant (p r B T : ℝ) : ℝ := 2 * (tangentConstant r + T * (1 + B / 4) ^ 2) / p ^ 4
def baseConstant (p r B T : ℝ) : ℝ := 2 * (T / p ^ 2) + 2 * meanConstant p r B T
def coercivityConstant (p r B T : ℝ) : ℝ :=
  5 / 4 + tangentConstant r + 5 / 4 * B * meanConstant p r B T + baseConstant p r B T
theorem bondSobolevSq_le_mul_bondQuadraticForm (hp : 0 < p) (hr : 0 < r) (hB : 0 < B)
    (hT : 0 < T) (hf : IsAdmissibleFamily p r B T s z D d v u dc) (b : ι → Fin 4 → ℂ) :
    bondSobolevSq s D b ≤ coercivityConstant p r B T * bondQuadraticForm s D d v u b := by
  obtain ⟨a, ha⟩ : ∃ a, a = bondNormSq (tangentPart D d b) z := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = ∑ m ∈ s.erase z, bondNormSq (tangentPart D d b) m := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ m ∈ s, D m * bondNormSq (tangentPart D d b) m := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ m ∈ s,
      ‖familyDivergence d b m - v m * weightedSiteSum s v (familyDivergence d b)‖ ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∑ μ, ‖weightedBondSum s u b μ‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Gm, hG⟩ : ∃ Gm, Gm = ‖weightedSiteSum s v (familyDivergence d b)‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ Lz, Lz = D z * ‖normalCoeff D d b z‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Lo, hLo⟩ : ∃ Lo, Lo = ∑ m ∈ s.erase z, D m * ‖normalCoeff D d b m‖ ^ 2 := ⟨_, rfl⟩
  have hchi : ∑ m ∈ s, ‖familyDivergence d b m‖ ^ 2 = R + Gm := by
    rw [hR, hG]
    exact sum_sq_norm_eq_rest_add_mean hf.site_sum_sq _
  have hE : bondDirichlet s D b = P + (R + Gm) := by
    simp only [bondDirichlet]
    rw [Finset.sum_congr rfl (fun m hm => weight_mul_bondNormSq_split hf hm b),
      Finset.sum_add_distrib, hchi, hP]
  have hF : bondQuadraticForm s D d v u b = P + R + Z := by
    simp only [bondQuadraticForm]
    rw [hE, ← hG, ← hZ]
    ring
  have hS : ∑ m ∈ s, bondNormSq b m = a + H + (Lz + Lo) := by
    rw [Finset.sum_congr rfl (fun m hm => bondNormSq_split hf hm b), Finset.sum_add_distrib,
      ← Finset.add_sum_erase s (fun m => bondNormSq (tangentPart D d b) m) hf.mem,
      ← Finset.add_sum_erase s (fun m => D m * ‖normalCoeff D d b m‖ ^ 2) hf.mem,
      ha, hH, hLz, hLo]
  have hN : bondSobolevSq s D b = P + (R + Gm) + (a + H + (Lz + Lo)) := by
    rw [bondSobolevSq_eq, hE, hS]
  have hsq : ∀ m, 0 ≤ bondNormSq (tangentPart D d b) m := fun m =>
    Finset.sum_nonneg fun μ _ => by positivity
  have hDz := hf.weight_nonneg hf.mem
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact Finset.sum_nonneg fun m hm => mul_nonneg (hf.weight_nonneg hm) (hsq m)
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact Finset.sum_nonneg fun m _ => by positivity
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    exact Finset.sum_nonneg fun m _ => by positivity
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact hsq z
  have h4H : 4 * H ≤ P := by
    rw [hP, hH, ← Finset.add_sum_erase s (fun m => D m * bondNormSq (tangentPart D d b) m) hf.mem,
      Finset.mul_sum]
    have h1 : ∑ m ∈ s.erase z, 4 * bondNormSq (tangentPart D d b) m ≤
        ∑ m ∈ s.erase z, D m * bondNormSq (tangentPart D d b) m :=
      Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_right
        (hf.four_le m (Finset.mem_of_mem_erase hm) (Finset.ne_of_mem_erase hm)) (hsq m)
    have h2 : 0 ≤ D z * bondNormSq (tangentPart D d b) z := mul_nonneg hDz (hsq z)
    linarith
  have h4L : 4 * Lo ≤ R + Gm := by
    rw [hLo, ← hchi, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun m hm => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset z s)
        (fun _ _ _ => by positivity))
    have h4 := hf.four_le m (Finset.mem_of_mem_erase hm) (Finset.ne_of_mem_erase hm)
    rw [sq_norm_familyDivergence_eq hf (Finset.mem_of_mem_erase hm) b]
    have hx : 0 ≤ ‖normalCoeff D d b m‖ ^ 2 := by positivity
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h4) (by linarith : (0 : ℝ) ≤ D m)) hx]
  obtain ⟨F, hFd⟩ : ∃ F, F = P + R + Z := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by
    rw [hFd]
    positivity
  obtain ⟨t2, ht2⟩ : ∃ t2, t2 =
      ‖(∑ m ∈ s, (v m : ℂ) * normalCoeff D d b m) / (v z : ℂ)‖ ^ 2 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t2 := by
    rw [ht2]
    positivity
  have hX : a + D z * t2 ≤ tangentConstant r * F := by
    have h1 := tangentPart_at_base_bound hp hr hf b
    rw [← ht2, ← ha, ← hZ, ← hH] at h1
    have h2 : r ^ 2 * (a + D z * t2) ≤ 2 * F := by
      rw [hFd]
      linarith
    have hr2 : 0 < r ^ 2 := by positivity
    have e : tangentConstant r * F = 2 * F / r ^ 2 := by
      simp only [tangentConstant]
      ring
    rw [e, le_div_iff₀ hr2]
    linarith
  have hDt : 0 ≤ D z * t2 := mul_nonneg hDz ht0
  have hg0 : 0 ≤ meanConstant p r B T := by
    simp only [meanConstant, tangentConstant]
    positivity
  have hk0 : 0 ≤ baseConstant p r B T := by
    simp only [baseConstant]
    positivity
  have hGL : Gm ≤ B * meanConstant p r B T * F ∧ Lz ≤ baseConstant p r B T * F := by
    rcases hDz.eq_or_lt with h0 | hpos
    · refine ⟨?_, ?_⟩
      · have hχ : familyDivergence d b z = 0 := by
          rw [← weight_mul_normalCoeff hf hf.mem b, ← h0]
          simp
        have h1 := sq_norm_weightedSiteSum_nonpos_of_weight_eq_zero hf h0.symm
          (familyDivergence d b) hχ
        rw [← hG] at h1
        have h2 : 0 ≤ B * meanConstant p r B T * F := by positivity
        linarith
      · rw [hLz, ← h0, zero_mul]
        positivity
    · obtain ⟨β2, hβ2⟩ : ∃ β2, β2 = ‖∑ m ∈ s, (v m : ℂ) * normalCoeff D d b m‖ ^ 2 := ⟨_, rfl⟩
      have hv1 := hf.site_sq_le_one
      have hb : β2 = v z ^ 2 * t2 := by
        have hv : (v z : ℂ) ≠ 0 := by
          have h1 : v z ≠ 0 := (lt_of_lt_of_le hp hf.site_lower).ne'
          exact_mod_cast h1
        have e : ∑ m ∈ s, (v m : ℂ) * normalCoeff D d b m =
            (v z : ℂ) * ((∑ m ∈ s, (v m : ℂ) * normalCoeff D d b m) / (v z : ℂ)) := by
          field_simp
        rw [hβ2, ht2]
        conv_lhs => rw [e]
        rw [norm_mul, mul_pow, sq_norm_real_eq]
      have hg : p ^ 4 * Gm ≤ 2 * D z * (D z * β2 + T * (1 + B / 4) ^ 2 * R) := by
        rw [hG, hβ2, hR]
        exact sq_norm_weightedSiteSum_le hp hf hpos (familyDivergence d b)
      have hDb : D z * β2 ≤ tangentConstant r * F := by
        rw [hb]
        have h1 : v z ^ 2 * t2 ≤ t2 := mul_le_of_le_one_left ht0 hv1
        have h2 : D z * (v z ^ 2 * t2) ≤ D z * t2 := mul_le_mul_of_nonneg_left h1 hDz
        linarith
      have hRF : R ≤ F := by
        rw [hFd]
        linarith
      have hTR : T * (1 + B / 4) ^ 2 * R ≤ T * (1 + B / 4) ^ 2 * F :=
        mul_le_mul_of_nonneg_left hRF (by positivity)
      have hp4 : 0 < p ^ 4 := by positivity
      have eg : p ^ 4 * meanConstant p r B T =
          2 * (tangentConstant r + T * (1 + B / 4) ^ 2) := by
        simp only [meanConstant]
        field_simp
      have hGD : Gm ≤ D z * meanConstant p r B T * F := by
        refine le_of_mul_le_mul_left ?_ hp4
        calc p ^ 4 * Gm ≤ 2 * D z * (D z * β2 + T * (1 + B / 4) ^ 2 * R) := hg
          _ ≤ 2 * D z * (tangentConstant r * F + T * (1 + B / 4) ^ 2 * F) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = D z * (2 * (tangentConstant r + T * (1 + B / 4) ^ 2)) * F := by ring
          _ = p ^ 4 * (D z * meanConstant p r B T * F) := by
              rw [← eg]
              ring
      refine ⟨hGD.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hf.le_bound hg0) hF0), ?_⟩
      have hρ := rest_at_base_le hf
        (fun m => familyDivergence d b m - v m * weightedSiteSum s v (familyDivergence d b))
        (sum_mul_sub_weightedSiteSum_eq_zero hf.site_sum_sq _)
      obtain ⟨q, hq⟩ : ∃ q, q =
          ‖familyDivergence d b z - v z * weightedSiteSum s v (familyDivergence d b)‖ ^ 2 :=
        ⟨_, rfl⟩
      have hρ' : v z ^ 2 * q ≤ (1 - v z ^ 2) * R := by
        rw [hq, hR]
        exact hρ
      have hq0 : 0 ≤ q := by
        rw [hq]
        positivity
      have hG0 : 0 ≤ Gm := by
        rw [hG]
        positivity
      have hp2 : p ^ 2 ≤ v z ^ 2 := pow_le_pow_left₀ hp.le hf.site_lower 2
      have h1 : p ^ 2 * q ≤ T * D z * R :=
        calc p ^ 2 * q ≤ v z ^ 2 * q := mul_le_mul_of_nonneg_right hp2 hq0
          _ ≤ (1 - v z ^ 2) * R := hρ'
          _ ≤ T * D z * R := mul_le_mul_of_nonneg_right (by linarith [hf.deficit_le]) hR0
      have hq1 : q ≤ T / p ^ 2 * D z * R := by
        have hp2' : 0 < p ^ 2 := by positivity
        have e : T / p ^ 2 * D z * R = T * D z * R / p ^ 2 := by ring
        rw [e, le_div_iff₀ hp2']
        linarith
      have hc : ‖familyDivergence d b z‖ ^ 2 ≤ 2 * q + 2 * (v z ^ 2 * Gm) := by
        have h := sq_norm_add_le_two_mul
          (familyDivergence d b z - v z * weightedSiteSum s v (familyDivergence d b))
          (v z * weightedSiteSum s v (familyDivergence d b))
        rw [sub_add_cancel, norm_mul, mul_pow, sq_norm_real_eq, ← hG, ← hq] at h
        exact h
      have hcz : ‖familyDivergence d b z‖ ^ 2 = D z * Lz := by
        rw [sq_norm_familyDivergence_eq hf hf.mem b, hLz]
        ring
      have h2 : v z ^ 2 * Gm ≤ Gm := mul_le_of_le_one_left hG0 hv1
      have h3 : T / p ^ 2 * D z * R ≤ T / p ^ 2 * D z * F :=
        mul_le_mul_of_nonneg_left hRF (by positivity)
      refine le_of_mul_le_mul_left ?_ hpos
      calc D z * Lz ≤ 2 * (T / p ^ 2 * D z * F) + 2 * (D z * meanConstant p r B T * F) := by
            rw [← hcz]
            linarith
        _ = D z * (baseConstant p r B T * F) := by
            simp only [baseConstant]
            ring
  obtain ⟨hGm, hLzb⟩ := hGL
  have e : coercivityConstant p r B T * F = 5 / 4 * F + tangentConstant r * F +
      5 / 4 * (B * meanConstant p r B T * F) + baseConstant p r B T * F := by
    simp only [coercivityConstant]
    ring
  rw [hF, ← hFd, hN, e]
  linarith
end Family
theorem finiteFamilyCoercivity_holds : FiniteFamilyCoercivity := by
  intro p r B T hp hr hB hT
  have hN1 : 1 ≤ coercivityConstant p r B T := by
    have h1 : 0 ≤ tangentConstant r := by
      simp only [tangentConstant]
      positivity
    have h2 : 0 ≤ meanConstant p r B T := by
      simp only [meanConstant]
      positivity
    have h3 : 0 ≤ baseConstant p r B T := by
      simp only [baseConstant]
      positivity
    have h4 : 0 ≤ 5 / 4 * B * meanConstant p r B T := by positivity
    simp only [coercivityConstant]
    linarith
  have hN0 : 0 < coercivityConstant p r B T := by linarith
  refine ⟨(coercivityConstant p r B T)⁻¹, ⟨inv_pos.2 hN0, inv_le_one_of_one_le₀ hN1⟩,
    min (p ^ 2 / 2) (3 / 5), ⟨lt_min (by positivity) (by norm_num),
      (min_le_right _ _).trans (by norm_num)⟩,
    min 1 (min (r ^ 2) (p ^ 2) / (B + 1)), ⟨lt_min one_pos (by positivity), min_le_left _ _⟩, ?_⟩
  intro ι s z D d v u dc hf
  classical
  refine ⟨fun b => ⟨?_, bondQuadraticForm_le hf b⟩,
    fun l => ⟨le_siteQuadraticForm hp hf l, siteQuadraticForm_le hf l⟩,
    fun μ => (min_le_right _ _).trans (le_bondResolventWeight hr hf μ),
    (min_le_right _ _).trans (le_siteResolventWeight hp hf)⟩
  rw [inv_mul_le_iff₀ hN0]
  exact bondSobolevSq_le_mul_bondQuadraticForm hp hr hB hT hf b
end YangMills.Construction.Coercivity
end
