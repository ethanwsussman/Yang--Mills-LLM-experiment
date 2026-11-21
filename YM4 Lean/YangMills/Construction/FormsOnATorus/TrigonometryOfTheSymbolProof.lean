import YangMills.Construction.FormsOnATorus.TrigonometryOfTheSymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
private lemma cos_sub_taylor_abs_le (t : ℝ) : |Real.cos t - 1 + t ^ 2 / 2| ≤ t ^ 4 / 2 := by
  by_cases h : |t| ≤ 1
  · have h1 := Real.cos_bound h
    have h2 : |t| ^ 4 = t ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
    rw [h2] at h1
    have h3 : Real.cos t - 1 + t ^ 2 / 2 = Real.cos t - (1 - t ^ 2 / 2) := by ring
    rw [h3]
    have h4 : (0 : ℝ) ≤ t ^ 4 := by positivity
    linarith
  · push_neg at h
    have h1 := Real.one_sub_sq_div_two_le_cos (x := t)
    have h2 := Real.cos_le_one t
    have h3 : 1 ≤ t ^ 2 := by
      have : 1 ≤ |t| ^ 2 := one_le_pow₀ h.le
      rwa [sq_abs] at this
    have h4 : t ^ 2 ≤ t ^ 4 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith
private lemma sin_half_prod_sub_abs_le (p : Fin 4 → ℝ) (i j : Fin 4) :
    |4 * Real.sin (p i / 2) * Real.sin (p j / 2) - p i * p j| ≤ 2 * momentumNormSq p ^ 2 := by
  have hl : ∀ l, p l ^ 2 ≤ momentumNormSq p := fun l =>
    Finset.single_le_sum (f := fun l => p l ^ 2) (fun _ _ => by positivity) (Finset.mem_univ l)
  set α := p i / 2 with hα
  set β := p j / 2 with hβ
  have e1 : p i = 2 * α := by simp only [hα]; ring
  have e2 : p j = 2 * β := by simp only [hβ]; ring
  have r1 := cos_sub_taylor_abs_le (α - β)
  have r2 := cos_sub_taylor_abs_le (α + β)
  have id1 : 4 * Real.sin α * Real.sin β = 2 * Real.cos (α - β) - 2 * Real.cos (α + β) := by
    rw [Real.cos_sub, Real.cos_add]; ring
  have h1 : (α - β) ^ 2 ≤ momentumNormSq p := by
    have a1 := hl i
    have a2 := hl j
    rw [e1] at a1
    rw [e2] at a2
    nlinarith [sq_nonneg (α + β)]
  have h2 : (α + β) ^ 2 ≤ momentumNormSq p := by
    have a1 := hl i
    have a2 := hl j
    rw [e1] at a1
    rw [e2] at a2
    nlinarith [sq_nonneg (α - β)]
  have h3 : (α - β) ^ 4 ≤ momentumNormSq p ^ 2 := by
    have : (α - β) ^ 4 = ((α - β) ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have h4 : (α + β) ^ 4 ≤ momentumNormSq p ^ 2 := by
    have : (α + β) ^ 4 = ((α + β) ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) h2 2
  rw [id1, e1, e2]
  rw [abs_le] at r1 r2 ⊢
  constructor <;> nlinarith [r1.1, r1.2, r2.1, r2.2]
private lemma lagrange_identity_four (a h : Fin 4 → ℝ) :
    ∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2), (a q.1 * h q.2 - a q.2 * h q.1) ^ 2 =
      (∑ l, h l ^ 2) * (∑ l, a l ^ 2) - (∑ l, a l * h l) ^ 2 := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_four]
  ring
private lemma jordan_sin_sq_le (t : ℝ) (ht : |t| ≤ Real.pi / 2) : (2 / Real.pi * t) ^ 2 ≤ Real.sin t ^ 2 := by
  rcases le_total 0 t with h | h
  · have h1 := Real.mul_le_sin h (by rwa [abs_of_nonneg h] at ht)
    exact pow_le_pow_left₀ (by positivity) h1 2
  · have h0 : 0 ≤ -t := by linarith
    have h1 := Real.mul_le_sin h0 (by rwa [abs_of_nonpos h] at ht)
    rw [Real.sin_neg] at h1
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    calc _ = (2 / Real.pi * -t) ^ 2 := by ring
      _ ≤ _ := h2
      _ = _ := by ring
private lemma momentumNormSq_le_sineSum (p : Fin 4 → ℝ) (hp : p ∈ brillouinBox) :
    4 / Real.pi ^ 2 * momentumNormSq p ≤ ∑ l, (2 * Real.sin (p l / 2)) ^ 2 := by
  unfold momentumNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  have h1 : |p l / 2| ≤ Real.pi / 2 := by
    have := hp.1 l
    have h2 := hp.2 l
    rw [abs_le]
    constructor <;> linarith
  have h3 := jordan_sin_sq_le _ h1
  have e1 : (2 / Real.pi * (p l / 2)) ^ 2 = p l ^ 2 / Real.pi ^ 2 := by
    field_simp
  rw [e1] at h3
  have e2 : (2 * Real.sin (p l / 2)) ^ 2 = 4 * Real.sin (p l / 2) ^ 2 := by ring
  rw [e2]
  have e3 : 4 / Real.pi ^ 2 * p l ^ 2 = 4 * (p l ^ 2 / Real.pi ^ 2) := by ring
  rw [e3]
  linarith
theorem latticeMomentumTrig : latticeMomentumTrigStatement :=
  ⟨cos_sub_taylor_abs_le, sin_half_prod_sub_abs_le, lagrange_identity_four, momentumNormSq_le_sineSum⟩
end YangMills.Construction.LimitForms
end
