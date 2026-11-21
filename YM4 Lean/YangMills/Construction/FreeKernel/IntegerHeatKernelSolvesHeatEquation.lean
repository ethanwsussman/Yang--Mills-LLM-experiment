import YangMills.Construction.FreeKernel.IntegerHeatEquation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.IntegerHeat
open YangMills.Construction.FreeKernel.UnitLattice YangMills.Construction.LatticeKernel Complex MeasureTheory
theorem continuous_laplacianSymbol : Continuous laplacianSymbol := by
  unfold laplacianSymbol
  fun_prop
theorem abs_laplacianSymbol_le (θ : ℝ) : |laplacianSymbol θ| ≤ 4 := by
  unfold laplacianSymbol
  have hup := Real.cos_le_one θ
  have hlow := Real.neg_one_le_cos θ
  rw [abs_le]
  constructor <;> linarith
theorem norm_exp_I_mul_int_mul (k : ℤ) (θ : ℝ) : ‖Complex.exp (I * (k : ℂ) * (θ : ℂ))‖ = 1 := by
  have h : I * (k : ℂ) * (θ : ℂ) = (((k : ℝ) * θ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]
theorem continuous_fourierIntegrand (t : ℝ) (k : ℤ) :
    Continuous fun θ : ℝ =>
      Complex.exp (I * (k : ℂ) * (θ : ℂ)) * (Real.exp (-t * laplacianSymbol θ) : ℂ) := by
  have h := continuous_laplacianSymbol
  fun_prop
theorem continuous_fourierIntegrand_deriv (t : ℝ) (k : ℤ) :
    Continuous fun θ : ℝ =>
      Complex.exp (I * (k : ℂ) * (θ : ℂ)) *
        ((Real.exp (-t * laplacianSymbol θ) * (-laplacianSymbol θ) : ℝ) : ℂ) := by
  have h := continuous_laplacianSymbol
  fun_prop
theorem hasDerivAt_fourierIntegrand (s θ : ℝ) (k : ℤ) :
    HasDerivAt
      (fun t : ℝ =>
        Complex.exp (I * (k : ℂ) * (θ : ℂ)) * (Real.exp (-t * laplacianSymbol θ) : ℂ))
      (Complex.exp (I * (k : ℂ) * (θ : ℂ)) *
        ((Real.exp (-s * laplacianSymbol θ) * (-laplacianSymbol θ) : ℝ) : ℂ)) s := by
  have hlin : HasDerivAt (fun t : ℝ => -t * laplacianSymbol θ) (-laplacianSymbol θ) s := by
    simpa using ((hasDerivAt_id s).neg).mul_const (laplacianSymbol θ)
  exact (hlin.exp.ofReal_comp).const_mul _
theorem norm_fourierIntegrand_deriv_le (T s θ : ℝ) (k : ℤ) (hs : s ∈ Metric.ball T 1) :
    ‖Complex.exp (I * (k : ℂ) * (θ : ℂ)) *
        ((Real.exp (-s * laplacianSymbol θ) * (-laplacianSymbol θ) : ℝ) : ℂ)‖ ≤
      Real.exp ((|T| + 1) * 4) * 4 := by
  rw [norm_mul, norm_exp_I_mul_int_mul, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_neg]
  have hsym := abs_laplacianSymbol_le θ
  have hs' : |s| ≤ |T| + 1 := by
    have hdist : |s - T| < 1 := by simpa [Real.dist_eq] using hs
    have htri : |s| ≤ |s - T| + |T| := by
      simpa using abs_add_le (s - T) T
    linarith
  have harg : -s * laplacianSymbol θ ≤ (|T| + 1) * 4 := by
    calc -s * laplacianSymbol θ ≤ |-s * laplacianSymbol θ| := le_abs_self _
      _ = |s| * |laplacianSymbol θ| := by rw [abs_mul, abs_neg]
      _ ≤ (|T| + 1) * 4 :=
        mul_le_mul hs' hsym (abs_nonneg _) (by positivity)
  exact mul_le_mul (Real.exp_le_exp.mpr harg) hsym (abs_nonneg _) (Real.exp_pos _).le
theorem hasDerivAt_integral_fourierIntegrand (T : ℝ) (k : ℤ) :
    HasDerivAt
      (fun t : ℝ => ∫ θ in (-Real.pi)..Real.pi,
        Complex.exp (I * (k : ℂ) * (θ : ℂ)) * (Real.exp (-t * laplacianSymbol θ) : ℂ))
      (∫ θ in (-Real.pi)..Real.pi,
        Complex.exp (I * (k : ℂ) * (θ : ℂ)) *
          ((Real.exp (-T * laplacianSymbol θ) * (-laplacianSymbol θ) : ℝ) : ℂ)) T := by
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (t : ℝ) (θ : ℝ) =>
      Complex.exp (I * (k : ℂ) * (θ : ℂ)) * (Real.exp (-t * laplacianSymbol θ) : ℂ))
    (F' := fun (t : ℝ) (θ : ℝ) =>
      Complex.exp (I * (k : ℂ) * (θ : ℂ)) *
        ((Real.exp (-t * laplacianSymbol θ) * (-laplacianSymbol θ) : ℝ) : ℂ))
    (bound := fun _ => Real.exp ((|T| + 1) * 4) * 4)
    (s := Metric.ball T 1) (Metric.ball_mem_nhds T one_pos)
    (Filter.Eventually.of_forall fun t => (continuous_fourierIntegrand t k).aestronglyMeasurable)
    ((continuous_fourierIntegrand T k).intervalIntegrable _ _)
    (continuous_fourierIntegrand_deriv T k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ s hs => norm_fourierIntegrand_deriv_le T s θ k hs)
    (continuous_const.intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun θ _ s _ => hasDerivAt_fourierIntegrand s θ k)).2
theorem fourierIntegrand_deriv_eq (T θ : ℝ) (k : ℤ) :
    Complex.exp (I * (k : ℂ) * (θ : ℂ)) *
        ((Real.exp (-T * laplacianSymbol θ) * (-laplacianSymbol θ) : ℝ) : ℂ) =
      Complex.exp (I * ((k + 1 : ℤ) : ℂ) * (θ : ℂ)) * (Real.exp (-T * laplacianSymbol θ) : ℂ) +
        Complex.exp (I * ((k - 1 : ℤ) : ℂ) * (θ : ℂ)) * (Real.exp (-T * laplacianSymbol θ) : ℂ) -
        2 * (Complex.exp (I * (k : ℂ) * (θ : ℂ)) * (Real.exp (-T * laplacianSymbol θ) : ℂ)) := by
  have hsucc : Complex.exp (I * ((k + 1 : ℤ) : ℂ) * (θ : ℂ)) =
      Complex.exp (I * (k : ℂ) * (θ : ℂ)) * Complex.exp ((θ : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpred : Complex.exp (I * ((k - 1 : ℤ) : ℂ) * (θ : ℂ)) =
      Complex.exp (I * (k : ℂ) * (θ : ℂ)) * Complex.exp (-(θ : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsym : ((laplacianSymbol θ : ℝ) : ℂ) =
      2 - (Complex.exp ((θ : ℂ) * I) + Complex.exp (-(θ : ℂ) * I)) := by
    rw [← Complex.two_cos]
    simp [laplacianSymbol]
  rw [hsucc, hpred]
  push_cast
  rw [hsym]
  ring
theorem hasDerivAt_discreteHeatKernel (T : ℝ) (k : ℤ) :
    HasDerivAt (fun t => discreteHeatKernel t k)
      (discreteHeatKernel T (k + 1) + discreteHeatKernel T (k - 1) - 2 * discreteHeatKernel T k) T := by
  have h := (hasDerivAt_integral_fourierIntegrand T k).const_mul (1 / (2 * (Real.pi : ℂ)))
  have hsplit : (∫ θ in (-Real.pi)..Real.pi,
        Complex.exp (I * (k : ℂ) * (θ : ℂ)) *
          ((Real.exp (-T * laplacianSymbol θ) * (-laplacianSymbol θ) : ℝ) : ℂ)) =
      (∫ θ in (-Real.pi)..Real.pi,
        Complex.exp (I * ((k + 1 : ℤ) : ℂ) * (θ : ℂ)) * (Real.exp (-T * laplacianSymbol θ) : ℂ)) +
      (∫ θ in (-Real.pi)..Real.pi,
        Complex.exp (I * ((k - 1 : ℤ) : ℂ) * (θ : ℂ)) * (Real.exp (-T * laplacianSymbol θ) : ℂ)) -
      2 * (∫ θ in (-Real.pi)..Real.pi,
        Complex.exp (I * (k : ℂ) * (θ : ℂ)) * (Real.exp (-T * laplacianSymbol θ) : ℂ)) := by
    have j0 := (continuous_fourierIntegrand T k).intervalIntegrable (μ := volume) (-Real.pi) Real.pi
    have j1 := (continuous_fourierIntegrand T (k + 1)).intervalIntegrable (μ := volume) (-Real.pi) Real.pi
    have j2 := (continuous_fourierIntegrand T (k - 1)).intervalIntegrable (μ := volume) (-Real.pi) Real.pi
    rw [← intervalIntegral.integral_add j1 j2, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (j1.add j2) (j0.const_mul 2)]
    exact intervalIntegral.integral_congr fun θ _ => fourierIntegrand_deriv_eq T θ k
  rw [hsplit] at h
  have hrhs : discreteHeatKernel T (k + 1) + discreteHeatKernel T (k - 1) - 2 * discreteHeatKernel T k =
      (1 / (2 * (Real.pi : ℂ))) *
        ((∫ θ in (-Real.pi)..Real.pi,
          Complex.exp (I * ((k + 1 : ℤ) : ℂ) * (θ : ℂ)) * (Real.exp (-T * laplacianSymbol θ) : ℂ)) +
        (∫ θ in (-Real.pi)..Real.pi,
          Complex.exp (I * ((k - 1 : ℤ) : ℂ) * (θ : ℂ)) * (Real.exp (-T * laplacianSymbol θ) : ℂ)) -
        2 * (∫ θ in (-Real.pi)..Real.pi,
          Complex.exp (I * (k : ℂ) * (θ : ℂ)) * (Real.exp (-T * laplacianSymbol θ) : ℂ))) := by
    unfold discreteHeatKernel
    ring
  rw [hrhs]
  exact h
theorem discreteHeatKernel_zero (k : ℤ) : discreteHeatKernel 0 k = if k = 0 then 1 else 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold discreteHeatKernel
  simp only [neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, mul_one]
  by_cases hk : k = 0
  · subst hk
    simp
    field_simp
    ring
  · rw [if_neg hk]
    have hc : I * (k : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
    rw [integral_exp_mul_complex hc]
    have hperiod : Complex.exp (I * (k : ℂ) * (Real.pi : ℂ)) =
        Complex.exp (I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
      have h : I * (k : ℂ) * (Real.pi : ℂ) =
          I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
        push_cast
        ring
      rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hperiod]
    simp
theorem integerHeatKernelEvolution_holds : FreeKernel.IntegerHeatKernelEvolution := by
  constructor
  · intro k
    unfold integerHeatKernel
    rw [discreteHeatKernel_zero]
    split_ifs <;> simp
  · intro T k
    have h : HasDerivAt (fun t => (discreteHeatKernel t k).re)
        (discreteHeatKernel T (k + 1) + discreteHeatKernel T (k - 1) - 2 * discreteHeatKernel T k).re T :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt T (hasDerivAt_discreteHeatKernel T k)
    have hre : (discreteHeatKernel T (k + 1) + discreteHeatKernel T (k - 1) - 2 * discreteHeatKernel T k).re =
        integerHeatKernel T (k + 1) + integerHeatKernel T (k - 1) - 2 * integerHeatKernel T k := by
      simp [integerHeatKernel]
    rw [hre] at h
    exact h
end YangMills.Construction.FreeKernel.IntegerHeat
