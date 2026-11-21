import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.ResponseInTheExpansion.PartsOfTheTotalOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.ResponseLessTheActionReturns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TermCalculus
theorem totalResponseSubAction_of_decomposition (hP : responseTermDecompositionStatement) :
    totalResponseSubActionStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt₀, g⟩ := hP a ha
  refine ⟨L₀, rt₀, hrt₀, fun T hTa hL hD hCd hOn hrt => ?_⟩
  obtain ⟨C, hC, g⟩ := g T hTa hL hD hCd hOn hrt
  refine ⟨32 * C + 1, fun K hKb => ?_⟩
  have hK0 : 0 < K.Kb := by linarith
  obtain ⟨y₀, g⟩ := g K hK0
  refine ⟨max y₀ (max T.floorMin (200 * T.B + 1)), fun y hy R A hK hA hArr => ?_⟩
  have e₀ : y₀ ≤ y := (le_max_left _ _).trans hy
  have f₁ := (le_max_right _ _).trans hy
  have hyB : 200 * T.B + 1 ≤ y := (le_max_right _ _).trans f₁
  have P := g y e₀ R A hK hA hArr
  have hon := hA.onFamily
  have hxy : y ≤ R.coupling := hon.le_coupling
  have hB1 : 1 ≤ T.B := hD.B_ge
  have hx1 : 1 ≤ R.coupling := by linarith
  have hx0 : 0 < R.coupling := by linarith
  have hmv := abs_le.1 hA.abs_sub_le
  have hx'0 : 0 < R.nextCoupling := by linarith [hmv.1]
  have hx'1 : R.nextCoupling ≤ 1.01 * R.coupling := by linarith [hmv.2]
  have hKf : K.Admissible R.params := hK ▸ hA.admissible.params_admissible
  have hη0 := hKf.η₃_pos
  have hη1 := hKf.η₃_le
  have hinv : R.coupling⁻¹ ≤ 1.01 * R.nextCoupling⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hx'1 (mul_pos (inv_pos.2 hx0) (inv_pos.2 hx'0)).le
    have l : R.nextCoupling * (R.coupling⁻¹ * R.nextCoupling⁻¹) = R.coupling⁻¹ := by field_simp
    have r : 1.01 * R.coupling * (R.coupling⁻¹ * R.nextCoupling⁻¹) = 1.01 * R.nextCoupling⁻¹ := by field_simp
    linarith
  have hxt : R.coupling ^ (-(3 / 2) : ℝ) ≤ R.coupling⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hi0 : 0 < R.coupling⁻¹ := by positivity
  have hsum := termBounds_add (termBounds_add (termBounds_add (termBounds_add P.frame_bounds P.linear_bounds)
    P.remainder_bounds) P.scoreTail_bounds) P.gas_bounds
  subst hK
  set u : ℝ := R.coupling⁻¹ with hu
  set u' : ℝ := R.nextCoupling⁻¹ with hu'
  have hCu : C * R.coupling ^ (-(3 / 2) : ℝ) ≤ C * u := mul_le_mul_of_nonneg_left hxt hC
  have hCv : C / R.coupling = C * u := by rw [hu, div_eq_mul_inv]
  have hKv : A.responseParams.Kb / R.coupling = A.responseParams.Kb * u := by rw [hu, div_eq_mul_inv]
  have h4 : 4 * C * u ≤ 1 / 8 * A.responseParams.Kb * u := by
    refine mul_le_mul_of_nonneg_right ?_ hi0.le
    linarith
  have hKu : A.responseParams.Kb * u ≤ 1.01 * (A.responseParams.Kb * u') := by
    have := mul_le_mul_of_nonneg_left hinv hK0.le
    linarith
  have hdiv : A.responseParams.Kb * u ≤ A.responseParams.Kb * u / A.responseParams.η₃ := by
    rw [le_div_iff₀ hη0]
    have : 0 ≤ A.responseParams.Kb * u := by positivity
    nlinarith
  have hdiv' : A.responseParams.Kb * u / A.responseParams.η₃ ≤
      1.01 * (A.responseParams.Kb * u' / A.responseParams.η₃) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hKu hη0.le
  have p5 : (2⁻¹ : ℝ) ^ 5 = 1 / 32 := by norm_num
  have p4 : (2⁻¹ : ℝ) ^ 4 = 1 / 16 := by norm_num
  have hz : 0 ≤ A.responseParams.Kb * u' := by positivity
  have hz' : 0 ≤ A.responseParams.Kb * u' / A.responseParams.η₃ := by positivity
  have hd : C * R.coupling ^ (-(3 / 2) : ℝ) + C / R.coupling + 2⁻¹ ^ 5 * (A.responseParams.Kb / R.coupling) +
      C * R.coupling ^ (-(3 / 2) : ℝ) + C * R.coupling ^ (-(3 / 2) : ℝ) ≤ 1 / 2 * (A.responseParams.Kb * u') := by
    rw [hCv, hKv, p5]
    linarith
  have hd₃ : C * R.coupling ^ (-(3 / 2) : ℝ) + C / R.coupling +
      2⁻¹ ^ 5 * (A.responseParams.Kb / R.coupling / A.responseParams.η₃) + C * R.coupling ^ (-(3 / 2) : ℝ) +
      C * R.coupling ^ (-(3 / 2) : ℝ) ≤ 1 / 2 * (A.responseParams.Kb * u' / A.responseParams.η₃) := by
    rw [hCv, hKv, p5]
    linarith
  have hc : C * R.coupling ^ (-(3 / 2) : ℝ) + C / R.coupling + 2⁻¹ ^ 4 * (A.responseParams.Kb / R.coupling) +
      C * R.coupling ^ (-(3 / 2) : ℝ) + C * R.coupling ^ (-(3 / 2) : ℝ) ≤ 1 / 2 * (A.responseParams.Kb * u') := by
    rw [hCv, hKv, p4]
    linarith
  have hb := termBounds_mono hd hd₃ hc hsum
  refine ⟨totalRemainderOfTerms A, ⟨hb.admissible, ?_, hb.centered_compare⟩, P.isTotalRemainder⟩
  intro n _ hn y' W hW k c X h1 h3 hX
  refine (hb.derivDecay n hn y' W hW k c X h1 h3 hX).trans (le_of_eq ?_)
  beta_reduce
  split_ifs <;> rfl
end YangMills.Construction.ResponseInTheExpansion
end
