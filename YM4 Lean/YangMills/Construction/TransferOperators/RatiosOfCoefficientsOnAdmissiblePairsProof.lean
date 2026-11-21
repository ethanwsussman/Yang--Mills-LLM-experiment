import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernelProof
import YangMills.Construction.TransferOperators.RatiosOfCoefficientsOnAdmissiblePairs
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.TransferOperators
noncomputable section
namespace YangMills.Construction.SpinHarmonics.CharCoeffRatioBound
def realCharCoeff (β : ℝ) (n : ℕ) : ℝ := (weightCharCoeff β ⟨n⟩).re
variable {β : ℝ}
theorem realCharCoeff_pos (hβ : ∀ j : HalfNatural, WeightCharCoeffBounds β j) (n : ℕ) :
    0 < realCharCoeff β n :=
  (hβ ⟨n⟩).2.1
theorem realCharCoeff_succ_ratio_le (hβ : ∀ j : HalfNatural, WeightCharCoeffBounds β j) (n : ℕ) :
    realCharCoeff β (n + 1) / realCharCoeff β n ≤
        besselRatioBound β * (1 + (n : ℝ) / 2) ∧
      realCharCoeff β n / realCharCoeff β (n + 1) ≤
        besselRatioBound β * (1 + (n : ℝ) / 2) := by
  obtain ⟨-, -, -, -, hle, hmax⟩ := hβ ⟨n⟩
  have hcomb := hle.trans hmax
  exact ⟨(le_max_left _ _).trans hcomb, (le_max_right _ _).trans hcomb⟩
theorem realCharCoeff_ratio_le_pow (hβ : ∀ j : HalfNatural, WeightCharCoeffBounds β j)
    {M : ℝ} (hM : 1 ≤ M)
    {top : ℕ} (hstep : ∀ t : ℕ, t < top → besselRatioBound β * (1 + (t : ℝ) / 2) ≤ M)
    (a k : ℕ) (hak : a + k ≤ top) :
    realCharCoeff β (a + k) / realCharCoeff β a ≤ M ^ k ∧
      realCharCoeff β a / realCharCoeff β (a + k) ≤ M ^ k := by
  induction k with
  | zero =>
    have hne := (realCharCoeff_pos hβ a).ne'
    simp [hne]
  | succ k ih =>
    obtain ⟨hup, hdown⟩ := ih (by omega)
    have hM' := hstep (a + k) (by omega)
    obtain ⟨hs₁, hs₂⟩ := realCharCoeff_succ_ratio_le hβ (a + k)
    have q₀ := realCharCoeff_pos hβ a
    have q₁ := realCharCoeff_pos hβ (a + k)
    have q₂ := realCharCoeff_pos hβ (a + k + 1)
    have hpow : 0 ≤ M ^ k := pow_nonneg (by linarith) k
    rw [← add_assoc, pow_succ]
    constructor
    · calc realCharCoeff β (a + k + 1) / realCharCoeff β a
          = (realCharCoeff β (a + k) / realCharCoeff β a) *
              (realCharCoeff β (a + k + 1) / realCharCoeff β (a + k)) := by
            field_simp
        _ ≤ M ^ k * M := mul_le_mul hup (hs₁.trans hM') (by positivity) hpow
    · calc realCharCoeff β a / realCharCoeff β (a + k + 1)
          = (realCharCoeff β a / realCharCoeff β (a + k)) *
              (realCharCoeff β (a + k) / realCharCoeff β (a + k + 1)) := by
            field_simp
        _ ≤ M ^ k * M := mul_le_mul hdown (hs₂.trans hM') (by positivity) hpow
theorem realCharCoeff_ratio_le_of_abs_sub_le (hβ : ∀ j : HalfNatural, WeightCharCoeffBounds β j)
    (hC : 4 ≤ besselRatioBound β) {m m' d : ℕ} {w : ℝ}
    (hd : |(m' : ℝ) / 2 - (m : ℝ) / 2| ≤ (d : ℝ) / 2) (hw : (m' : ℝ) / 2 ≤ w) (hw0 : 0 ≤ w) :
    realCharCoeff β m / realCharCoeff β m' ≤
      (besselRatioBound β * (1 + (d : ℝ)) * (1 + w)) ^ d := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hone : 1 ≤ (1 + (d : ℝ)) * (1 + w) := by nlinarith [mul_nonneg hd0 hw0]
  have hM : 1 ≤ besselRatioBound β * (1 + (d : ℝ)) * (1 + w) := by
    rw [mul_assoc]; nlinarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hd
  have hm : m ≤ m' + d := by
    have : (m : ℝ) ≤ (m' : ℝ) + d := by linarith
    exact_mod_cast this
  have hm' : m' ≤ m + d := by
    have : (m' : ℝ) ≤ (m : ℝ) + d := by linarith
    exact_mod_cast this
  have hstep : ∀ t : ℕ, t < m' + d → besselRatioBound β * (1 + (t : ℝ) / 2) ≤
      besselRatioBound β * (1 + (d : ℝ)) * (1 + w) := by
    intro t ht
    have ht' : (t : ℝ) + 1 ≤ (m' : ℝ) + d := by exact_mod_cast ht
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    nlinarith [mul_nonneg hd0 hw0]
  rcases le_total m m' with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    refine ((realCharCoeff_ratio_le_pow hβ hM hstep m k (by omega)).2).trans ?_
    exact pow_le_pow_right₀ hM (by omega)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    refine ((realCharCoeff_ratio_le_pow hβ hM hstep m' k hm).1).trans ?_
    exact pow_le_pow_right₀ hM (by omega)
theorem halfNatural_toReal_nonneg (t : HalfNatural) : 0 ≤ t.toReal := by apply _root_.YangMills.Construction.TransferOperators.SqrtLinkFacts.halfNatural_toReal_nonneg <;> assumption
theorem charCoeffRatioBound_holds (h : BondWeightCharCoeffStatement) :
    CharCoeffRatioBoundStatement := by
  intro β K _ D l l' hβ hadm
  obtain ⟨-, hall⟩ := h
  obtain ⟨-, hb, hC, -, -⟩ := hall β hβ
  let _ : Fintype K := Fintype.ofFinite K
  have hW : ∀ j : K → HalfNatural, weightSum j = ∑ b, (j b).toReal := fun j =>
    finsum_eq_sum_of_fintype _
  have hW0 : 0 ≤ weightSum l' := by
    rw [hW]; exact Finset.sum_nonneg fun b _ => halfNatural_toReal_nonneg _
  have hWl : 0 ≤ weightSum l := by
    rw [hW]; exact Finset.sum_nonneg fun b _ => halfNatural_toReal_nonneg _
  have hWb : ∀ b, (l' b).toReal ≤ weightSum l' := fun b => by
    rw [hW]
    exact Finset.single_le_sum (f := fun b => (l' b).toReal)
      (fun b _ => halfNatural_toReal_nonneg _) (Finset.mem_univ b)
  have hS : ((degreeTotal D : ℕ) : ℝ) = ∑ b, (D b : ℝ) := by
    rw [degreeTotal, finsum_eq_sum_of_fintype, Nat.cast_sum]
  have hc : ∀ t : HalfNatural, weightCharCoeff β t = (realCharCoeff β t.doubled : ℂ) := by
    intro t
    change weightCharCoeff β t = ((weightCharCoeff β t).re : ℂ)
    rw [(hb t).1, Complex.ofReal_re]
  have hr : charCoeffRatio β l l' =
      ((∏ b, (realCharCoeff β (l b).doubled / realCharCoeff β (l' b).doubled) : ℝ) : ℂ) := by
    simp only [charCoeffRatio, TransferOperators.charCoeffProd, finprod_eq_prod_of_fintype, hc]
    rw [Finset.prod_div_distrib]
    push_cast
    rfl
  have hnn : ∀ b, 0 ≤ realCharCoeff β (l b).doubled / realCharCoeff β (l' b).doubled :=
    fun b => (div_pos (realCharCoeff_pos hb _) (realCharCoeff_pos hb _)).le
  constructor
  · rw [hr, Complex.norm_real, Real.norm_of_nonneg (Finset.prod_nonneg fun b _ => hnn b)]
    calc ∏ b, (realCharCoeff β (l b).doubled / realCharCoeff β (l' b).doubled)
        ≤ ∏ b, (besselRatioBound β * (1 + (D b : ℝ)) * (1 + weightSum l')) ^ D b :=
          Finset.prod_le_prod (fun b _ => hnn b) fun b _ =>
            realCharCoeff_ratio_le_of_abs_sub_le hb hC (hadm b) (hWb b) hW0
      _ = (∏ᶠ b, (besselRatioBound β * (1 + (D b : ℝ))) ^ D b) *
            (1 + weightSum l') ^ degreeTotal D := by
          rw [finprod_eq_prod_of_fintype, degreeTotal, finsum_eq_sum_of_fintype,
            ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun b _ => mul_pow _ _ _
  · have hsum : weightSum l' ≤ weightSum l + (degreeTotal D : ℝ) / 2 := by
      rw [hW, hW, hS, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun b _ => ?_
      have := (abs_le.mp (hadm b)).2
      linarith
    have hS0 : (0 : ℝ) ≤ (degreeTotal D : ℝ) / 2 := by positivity
    nlinarith [mul_nonneg hS0 hWl]
end YangMills.Construction.SpinHarmonics.CharCoeffRatioBound
end
