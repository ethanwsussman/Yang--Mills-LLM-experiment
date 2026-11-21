import YangMills.Construction.FreeKernel.DiscreteHeatKernelSeries
import YangMills.Construction.FreeKernel.IntegerHeatKernelSolvesHeatEquation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.HeatKernelSeries
open Complex YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
def seriesTerm (t : ℝ) (j : ℤ) (l : ℕ) : ℝ :=
  t ^ (2 * l + j.natAbs) / ((l.factorial : ℝ) * ((l + j.natAbs).factorial : ℝ))
def diffMinEquiv : ℤ × ℕ ≃ ℕ × ℕ where
  toFun p := (p.2 + p.1.toNat, p.2 + (-p.1).toNat)
  invFun p := ((p.1 : ℤ) - p.2, min p.1 p.2)
  left_inv := by
    rintro ⟨j, l⟩
    simp only [Prod.mk.injEq]
    omega
  right_inv := by
    rintro ⟨a, b⟩
    simp only [Prod.mk.injEq]
    omega
theorem hasSum_expSeries_complex (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
  simpa [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp z
theorem summable_norm_expSeries_complex (z : ℂ) :
    Summable (fun n : ℕ => ‖z ^ n / (n.factorial : ℂ)‖) := by
  simpa [norm_pow, Complex.norm_natCast] using Real.summable_pow_div_factorial ‖z‖
theorem hasSum_exp_mul_exp (z w : ℂ) :
    HasSum (fun p : ℕ × ℕ => z ^ p.1 / (p.1.factorial : ℂ) * (w ^ p.2 / (p.2.factorial : ℂ)))
      (Complex.exp z * Complex.exp w) := by
  have hs : Summable (fun p : ℕ × ℕ =>
      z ^ p.1 / (p.1.factorial : ℂ) * (w ^ p.2 / (p.2.factorial : ℂ))) :=
    summable_mul_of_summable_norm (f := fun n : ℕ => z ^ n / (n.factorial : ℂ))
      (g := fun n : ℕ => w ^ n / (n.factorial : ℂ))
      (summable_norm_expSeries_complex z) (summable_norm_expSeries_complex w)
  exact HasSum.mul (f := fun n : ℕ => z ^ n / (n.factorial : ℂ))
    (g := fun n : ℕ => w ^ n / (n.factorial : ℂ)) (hasSum_expSeries_complex z)
    (hasSum_expSeries_complex w) hs
theorem diffMinEquiv_arith (j : ℤ) (l : ℕ) :
    (l + j.toNat) + (l + (-j).toNat) = 2 * l + j.natAbs ∧
    (l + j.toNat).factorial * (l + (-j).toNat).factorial =
      l.factorial * (l + j.natAbs).factorial ∧
    (((l + j.toNat : ℕ) : ℤ) - ((l + (-j).toNat : ℕ) : ℤ)) = j := by
  refine ⟨by omega, ?_, by omega⟩
  rcases le_total 0 j with h | h
  · have h1 : j.toNat = j.natAbs := by omega
    have h2 : (-j).toNat = 0 := by omega
    rw [h1, h2, Nat.add_zero, Nat.mul_comm]
  · have h1 : j.toNat = 0 := by omega
    have h2 : (-j).toNat = j.natAbs := by omega
    rw [h1, h2, Nat.add_zero]
theorem exp_product_term_eq (t θ : ℝ) (j : ℤ) (l : ℕ) :
    ((t : ℂ) * Complex.exp (I * (θ : ℂ))) ^ (l + j.toNat) / ((l + j.toNat).factorial : ℂ) *
      (((t : ℂ) * Complex.exp (-(I * (θ : ℂ)))) ^ (l + (-j).toNat) /
        ((l + (-j).toNat).factorial : ℂ)) =
    ((seriesTerm t j l : ℝ) : ℂ) * Complex.exp (I * (j : ℂ) * (θ : ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := diffMinEquiv_arith j l
  generalize l + j.toNat = a at *
  generalize l + (-j).toNat = b at *
  have hj : (j : ℂ) = (a : ℂ) - (b : ℂ) := by
    rw [← h3]
    push_cast
    ring
  have hph : Complex.exp (I * (θ : ℂ)) ^ a * Complex.exp (-(I * (θ : ℂ))) ^ b =
      Complex.exp (I * (j : ℂ) * (θ : ℂ)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, hj]
    congr 1
    ring
  have hfac : (a.factorial : ℂ) * (b.factorial : ℂ) =
      (l.factorial : ℂ) * ((l + j.natAbs).factorial : ℂ) := by
    exact_mod_cast h2
  have ha : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hb : (b.factorial : ℂ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  simp only [seriesTerm]
  push_cast
  rw [← h1, ← hfac, ← hph, pow_add, mul_pow, mul_pow]
  field_simp
theorem hasSum_seriesTerm_phase (t θ : ℝ) :
    HasSum (fun p : ℤ × ℕ => ((seriesTerm t p.1 p.2 : ℝ) : ℂ) *
        Complex.exp (I * (p.1 : ℂ) * (θ : ℂ)))
      (Complex.exp (((2 * t * Real.cos θ : ℝ)) : ℂ)) := by
  have h := (diffMinEquiv.hasSum_iff).2 (hasSum_exp_mul_exp ((t : ℂ) * Complex.exp (I * (θ : ℂ)))
    ((t : ℂ) * Complex.exp (-(I * (θ : ℂ)))))
  have e : Complex.exp ((t : ℂ) * Complex.exp (I * (θ : ℂ))) *
      Complex.exp ((t : ℂ) * Complex.exp (-(I * (θ : ℂ)))) =
      Complex.exp (((2 * t * Real.cos θ : ℝ)) : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    rw [Complex.cos]
    have e1 : (θ : ℂ) * I = I * (θ : ℂ) := mul_comm _ _
    have e2 : -(θ : ℂ) * I = -(I * (θ : ℂ)) := by ring
    rw [e1, e2]
    ring
  rw [e] at h
  have hfun : (fun p : ℤ × ℕ => ((seriesTerm t p.1 p.2 : ℝ) : ℂ) *
      Complex.exp (I * (p.1 : ℂ) * (θ : ℂ))) =
      (fun p : ℕ × ℕ => ((t : ℂ) * Complex.exp (I * (θ : ℂ))) ^ p.1 / (p.1.factorial : ℂ) *
        (((t : ℂ) * Complex.exp (-(I * (θ : ℂ)))) ^ p.2 / (p.2.factorial : ℂ))) ∘ diffMinEquiv := by
    funext p
    exact (exp_product_term_eq t θ p.1 p.2).symm
  rw [hfun]
  exact h
theorem hasSum_seriesTerm (t : ℝ) :
    HasSum (fun p : ℤ × ℕ => seriesTerm t p.1 p.2) (Real.exp (2 * t)) := by
  have h := hasSum_seriesTerm_phase t 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, Real.cos_zero] at h
  rw [← Complex.ofReal_exp] at h
  exact Complex.hasSum_ofReal.1 h
def besselCoeff (t : ℝ) (j : ℤ) : ℝ :=
  ∑' l : ℕ, seriesTerm t j l
theorem summable_seriesTerm (t : ℝ) (j : ℤ) : Summable (seriesTerm t j) :=
  (hasSum_seriesTerm t).summable.prod_factor j
theorem hasSum_besselCoeff (t : ℝ) : HasSum (besselCoeff t) (Real.exp (2 * t)) :=
  (hasSum_seriesTerm t).prod_fiberwise fun j => (summable_seriesTerm t j).hasSum
theorem hasSum_besselCoeff_phase (t θ : ℝ) :
    HasSum (fun j : ℤ => ((besselCoeff t j : ℝ) : ℂ) * Complex.exp (I * (j : ℂ) * (θ : ℂ)))
      (Complex.exp (((2 * t * Real.cos θ : ℝ)) : ℂ)) :=
  (hasSum_seriesTerm_phase t θ).prod_fiberwise fun j =>
    (Complex.hasSum_ofReal.2 (summable_seriesTerm t j).hasSum).mul_right _
theorem seriesTerm_nonneg {t : ℝ} (ht : 0 ≤ t) (j : ℤ) (l : ℕ) : 0 ≤ seriesTerm t j l := by
  unfold seriesTerm
  positivity
theorem besselCoeff_pos {t : ℝ} (ht : 0 < t) (j : ℤ) : 0 < besselCoeff t j := by
  refine (summable_seriesTerm t j).tsum_pos (seriesTerm_nonneg ht.le j) 0 ?_
  unfold seriesTerm
  positivity
theorem besselCoeff_neg (t : ℝ) (j : ℤ) : besselCoeff t (-j) = besselCoeff t j := by
  simp [besselCoeff, seriesTerm]
theorem integral_exp_int_mul_I (n : ℤ) :
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (n : ℂ) * (θ : ℂ)) =
      if n = 0 then 2 * (Real.pi : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp
    ring
  · have hc : I * (n : ℂ) ≠ 0 := by simp [h]
    rw [integral_exp_mul_complex hc]
    have e : Complex.exp (I * (n : ℂ) * (Real.pi : ℂ)) =
        Complex.exp (I * (n : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
      have := Complex.exp_int_mul_two_pi_mul_I n
      rw [← mul_one (Complex.exp (I * (n : ℂ) * ((-Real.pi : ℝ) : ℂ))), ← this, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e, sub_self, zero_div]
theorem exp_neg_mul_laplacianSymbol (t θ : ℝ) :
    Real.exp (-t * laplacianSymbol θ) = Real.exp (-2 * t) * Real.exp (2 * t * Real.cos θ) := by
  rw [← Real.exp_add, laplacianSymbol]
  congr 1
  ring
theorem norm_exp_int_phase (n : ℤ) (θ : ℝ) : ‖Complex.exp (I * (n : ℂ) * (θ : ℂ))‖ = 1 := by apply _root_.YangMills.Construction.FreeKernel.IntegerHeat.norm_exp_I_mul_int_mul <;> assumption
theorem discreteHeatKernel_eq {t : ℝ} (ht : 0 < t) (j : ℤ) :
    discreteHeatKernel t j = ((Real.exp (-2 * t) * besselCoeff t j : ℝ) : ℂ) := by
  have hpos : ∀ k, 0 ≤ besselCoeff t k := fun k => (besselCoeff_pos ht k).le
  set F : ℤ → ℝ → ℂ := fun k θ => Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
    (((Real.exp (-2 * t) : ℝ) : ℂ) *
      (((besselCoeff t k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * (θ : ℂ)))) with hF
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := -Real.pi) (b := Real.pi) (F := F)
    (f := fun θ => Complex.exp (I * (j : ℂ) * (θ : ℂ)) *
      ((Real.exp (-t * laplacianSymbol θ) : ℝ) : ℂ))
    (fun k _ => Real.exp (-2 * t) * besselCoeff t k)
    (fun k => by
      have : Continuous (F k) := by
        simp only [hF]
        fun_prop
      exact this.aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall fun θ _ => by
      simp only [hF, norm_mul, norm_exp_int_phase, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_nonneg (hpos k), one_mul, mul_one]
      exact le_refl _)
    (Filter.Eventually.of_forall fun θ _ => (hasSum_besselCoeff t).summable.mul_left _)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => by
      have h := ((hasSum_besselCoeff_phase t θ).mul_left
        ((Real.exp (-2 * t) : ℝ) : ℂ)).mul_left (Complex.exp (I * (j : ℂ) * (θ : ℂ)))
      rw [exp_neg_mul_laplacianSymbol, Complex.ofReal_mul, Complex.ofReal_exp (2 * t * Real.cos θ)]
      exact h)
  have hint : ∀ k : ℤ, ∫ θ in (-Real.pi)..Real.pi, F k θ =
      if k = -j then
        ((Real.exp (-2 * t) : ℝ) : ℂ) * ((besselCoeff t (-j) : ℝ) : ℂ) * (2 * (Real.pi : ℂ))
      else 0 := by
    intro k
    have e : ∀ θ : ℝ, F k θ = ((Real.exp (-2 * t) : ℝ) : ℂ) * ((besselCoeff t k : ℝ) : ℂ) *
        Complex.exp (I * ((j + k : ℤ) : ℂ) * (θ : ℂ)) := by
      intro θ
      have : I * ((j + k : ℤ) : ℂ) * (θ : ℂ) =
          I * (j : ℂ) * (θ : ℂ) + I * (k : ℂ) * (θ : ℂ) := by
        push_cast
        ring
      simp only [hF]
      rw [this, Complex.exp_add]
      ring
    simp only [e]
    rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
    by_cases hk : k = -j
    · simp [hk]
    · have : j + k ≠ 0 := fun h => hk (by omega)
      simp [hk, this]
  have hone : HasSum (fun k : ℤ => ∫ θ in (-Real.pi)..Real.pi, F k θ)
      (((Real.exp (-2 * t) : ℝ) : ℂ) * ((besselCoeff t (-j) : ℝ) : ℂ) * (2 * (Real.pi : ℂ))) := by
    simp only [hint]
    exact hasSum_ite_eq (-j) _
  have hval := hsum.unique hone
  unfold discreteHeatKernel
  rw [hval, besselCoeff_neg]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
theorem re_discreteHeatKernel {t : ℝ} (ht : 0 < t) (j : ℤ) :
    (discreteHeatKernel t j).re = Real.exp (-2 * t) * besselCoeff t j := by
  rw [discreteHeatKernel_eq ht, Complex.ofReal_re]
theorem hasSum_discreteHeatKernel_fourier {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    HasSum (fun j : ℤ => discreteHeatKernel t j * Complex.exp (-(I * (j : ℂ) * (θ : ℂ))))
      ((Real.exp (-t * laplacianSymbol θ) : ℝ) : ℂ) := by
  have h := (hasSum_besselCoeff_phase t (-θ)).mul_left ((Real.exp (-2 * t) : ℝ) : ℂ)
  rw [Real.cos_neg] at h
  rw [exp_neg_mul_laplacianSymbol, Complex.ofReal_mul, Complex.ofReal_exp (2 * t * Real.cos θ)]
  have hfun : (fun j : ℤ => discreteHeatKernel t j * Complex.exp (-(I * (j : ℂ) * (θ : ℂ)))) =
      fun j : ℤ => ((Real.exp (-2 * t) : ℝ) : ℂ) * (((besselCoeff t j : ℝ) : ℂ) *
        Complex.exp (I * (j : ℂ) * ((-θ : ℝ) : ℂ))) := by
    funext j
    have e : -(I * (j : ℂ) * (θ : ℂ)) = I * (j : ℂ) * ((-θ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [discreteHeatKernel_eq ht, Complex.ofReal_mul, mul_assoc, e]
  rw [hfun]
  exact h
theorem besselCoeff_le {t : ℝ} (ht : 0 < t) (j : ℤ) :
    besselCoeff t j ≤ t ^ j.natAbs / (j.natAbs.factorial : ℝ) * Real.exp (t ^ 2) := by
  have hexp : HasSum (fun l : ℕ => (t ^ 2) ^ l / (l.factorial : ℝ)) (Real.exp (t ^ 2)) := by
    have h := hasSum_expSeries_complex (((t ^ 2 : ℝ)) : ℂ)
    rw [← Complex.ofReal_exp] at h
    refine Complex.hasSum_ofReal.1 ?_
    have hfun : (fun l : ℕ => (((t ^ 2) ^ l / (l.factorial : ℝ) : ℝ) : ℂ)) =
        fun l : ℕ => (((t ^ 2 : ℝ)) : ℂ) ^ l / (l.factorial : ℂ) := by
      funext l
      push_cast
      rfl
    rw [hfun]
    exact h
  have hb := hexp.mul_left (t ^ j.natAbs / (j.natAbs.factorial : ℝ))
  refine hasSum_le (fun l => ?_) (summable_seriesTerm t j).hasSum hb
  have hm : (j.natAbs.factorial : ℝ) ≤ ((l + j.natAbs).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hl : (0 : ℝ) < (l.factorial : ℝ) := by exact_mod_cast l.factorial_pos
  have e : t ^ j.natAbs / (j.natAbs.factorial : ℝ) * ((t ^ 2) ^ l / (l.factorial : ℝ)) =
      t ^ (2 * l + j.natAbs) / ((l.factorial : ℝ) * (j.natAbs.factorial : ℝ)) := by
    rw [pow_add, pow_mul]
    field_simp
  rw [e]
  unfold seriesTerm
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hm hl.le)
theorem discreteHeatKernelSeries_holds : DiscreteHeatKernelSeries := by
  unfold DiscreteHeatKernelSeries
  refine ⟨fun t ht j => ⟨summable_seriesTerm t j, discreteHeatKernel_eq ht j⟩, fun t ht j => ?_,
    fun t ht j => ?_, fun t ht => ?_, fun t ht θ => ⟨?_, hasSum_discreteHeatKernel_fourier ht θ⟩,
    fun t ht ht1 j => ?_⟩
  · rw [discreteHeatKernel_eq ht]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    exact mul_pos (Real.exp_pos _) (besselCoeff_pos ht j)
  · rw [discreteHeatKernel_eq ht, discreteHeatKernel_eq ht, besselCoeff_neg]
  · have h := hasSum_discreteHeatKernel_fourier ht 0
    simpa [laplacianSymbol] using h
  · refine ((hasSum_besselCoeff t).summable.mul_left (Real.exp (-2 * t))).congr fun j => ?_
    have e : -(I * (j : ℂ) * (θ : ℂ)) = I * ((-j : ℤ) : ℂ) * (θ : ℂ) := by
      push_cast
      ring
    rw [norm_mul, e, norm_exp_int_phase, discreteHeatKernel_eq ht, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (besselCoeff_pos ht j)), mul_one]
  · rw [re_discreteHeatKernel ht, shiftConstant]
    have hA : 0 ≤ t ^ j.natAbs / (j.natAbs.factorial : ℝ) := by positivity
    calc Real.exp (-2 * t) * besselCoeff t j
        ≤ Real.exp (-2 * t) *
            (t ^ j.natAbs / (j.natAbs.factorial : ℝ) * Real.exp (t ^ 2)) :=
          mul_le_mul_of_nonneg_left (besselCoeff_le ht j) (Real.exp_pos _).le
      _ = Real.exp (-2 * t + t ^ 2) * (t ^ j.natAbs / (j.natAbs.factorial : ℝ)) := by
          rw [Real.exp_add]
          ring
      _ ≤ Real.exp 1 * (t ^ j.natAbs / (j.natAbs.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hA
end YangMills.Construction.FreeKernel.HeatKernelSeries
end
