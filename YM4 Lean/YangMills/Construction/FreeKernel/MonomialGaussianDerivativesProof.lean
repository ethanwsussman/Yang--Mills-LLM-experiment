import YangMills.Construction.Constants.HeatKernelNumbersFinite
import YangMills.Construction.FreeKernel.GaussianTimesVanishingFunction
import YangMills.Construction.FreeKernel.MonomialFactorDerivatives
import YangMills.Construction.FreeKernel.MonomialGaussianDerivatives
import YangMills.Construction.FreeKernel.SymbolDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.MonomialGaussian
open Complex MeasureTheory Filter Topology YangMills.Construction.LatticeKernel YangMills.Construction.Constants.HeatKernel
lemma iteratedDeriv_ofReal_comp {f : ℝ → ℝ} (hf : ∀ m : ℕ, ContDiff ℝ m f) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (f x : ℂ)) = fun x => ((iteratedDeriv n f x : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hdiff : DifferentiableAt ℝ (iteratedDeriv n f) x :=
      ((hf (n + 1)).differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n)) x
    rw [iteratedDeriv_succ]
    exact hdiff.hasDerivAt.ofReal_comp.deriv
lemma enorm_ofReal_eq_ofReal_abs (r : ℝ) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal |r| := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
lemma enorm_iteratedDeriv_gaussian_le (hsym : LatticeKernel.SymbolDerivativeBounds) {t : ℝ}
    (ht : 0 < t) (k : ℕ) (y : ℝ) :
    ‖iteratedDeriv k (fun x : ℝ => (Real.exp (-t * x ^ 2) : ℂ)) y‖ₑ ≤
      weightedFactorialPower k * ENNReal.ofReal (t ^ ((k : ℝ) / 2) * Real.exp (-(heatDecay * t * y ^ 2))) := by
  obtain ⟨-, -, -, -, hexp⟩ := hsym
  obtain ⟨hfirst, hsecond⟩ := hexp k t 0 y (Or.inr ⟨rfl, ht⟩)
  have hzero : ∀ x : ℝ, homotopySymbol 0 x = x ^ 2 := fun x => by simp [homotopySymbol]
  simp only [hzero] at hfirst hsecond
  have hsmooth : ∀ m : ℕ, ContDiff ℝ m (fun x : ℝ => Real.exp (-t * x ^ 2)) := fun m => by fun_prop
  rw [iteratedDeriv_ofReal_comp hsmooth, enorm_ofReal_eq_ofReal_abs]
  exact (ENNReal.ofReal_le_ofReal hfirst).trans hsecond
lemma tendsto_exp_neg_mul_sq {l : Filter ℝ} (hl : Tendsto (fun y : ℝ => y ^ 2) l atTop) {a : ℝ}
    (ha : 0 < a) : Tendsto (fun y : ℝ => Real.exp (-(a * y ^ 2))) l (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hl.const_mul_atTop ha))
lemma tendsto_zero_of_enorm_le {g : ℝ → ℂ} {K a : ℝ} {D : ENNReal} (hD : D ≠ ⊤) (hK : 0 ≤ K)
    {C : ℝ} (hC : 0 ≤ C) {l : Filter ℝ} (ha : Tendsto (fun y : ℝ => Real.exp (-(a * y ^ 2))) l (𝓝 0))
    (hbound : ∀ y, ‖g y‖ₑ ≤ ENNReal.ofReal C * D * ENNReal.ofReal (K * Real.exp (-(a * y ^ 2)))) :
    Tendsto g l (𝓝 0) := by
  have hpoint : ∀ y, ‖g y‖ ≤ C * D.toReal * K * Real.exp (-(a * y ^ 2)) := fun y => by
    have h := hbound y
    rw [← ENNReal.ofReal_toReal hD, ← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (by positivity),
      ← ofReal_norm] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    calc ‖g y‖ ≤ _ := h'
      _ = _ := by ring
  have hlim := ha.const_mul (C * D.toReal * K)
  rw [mul_zero] at hlim
  exact squeeze_zero_norm hpoint hlim
theorem monomialGaussianDerivativeBounds_holds (hvan : FreeKernel.VanishingTimesGaussianBound)
    (hsym : LatticeKernel.SymbolDerivativeBounds)
    (hmono : FreeKernel.MonomialFactorDerivativeBounds)
    (hnum : Constants.HeatKernel.finite_and_pos) : FreeKernel.MonomialGaussianDerivativeBounds := by
  intro α t ht k
  have htpos : 0 < t := by linarith
  obtain ⟨hsy, hrate, -, -, -, -, -, hmom, -⟩ := hnum
  have hmomfin : binomialMoment k (diffOrder α) ≠ ⊤ := (hmom k (diffOrder α)).1
  have hpow : ∀ m : ℕ, ContDiff ℝ m (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder α) := fun m =>
    (contDiff_const.mul Complex.ofRealCLM.contDiff).pow _
  have hgauss : ∀ m : ℕ, ContDiff ℝ m (fun x : ℝ => (Real.exp (-t * x ^ 2) : ℂ)) := fun m => by
    have h : ContDiff ℝ m (fun x : ℝ => Real.exp (-t * x ^ 2)) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp h
  have main := hvan k (diffOrder α) symmetryConstant t Set.univ
    (fun x : ℝ => (I * (x : ℂ)) ^ diffOrder α)
    (fun x : ℝ => (Real.exp (-t * x ^ 2) : ℂ)) hsy.le ht Set.ordConnected_univ
    (hpow k).contDiffOn (hgauss k).contDiffOn
    (fun j _ y _ => by
      simp only [iteratedDerivWithin_univ]
      exact ⟨hmono.1 α j y, enorm_iteratedDeriv_gaussian_le hsym htpos j y⟩)
  simp only [iteratedDerivWithin_univ, Set.mem_univ, forall_true_left, Measure.restrict_univ] at main
  obtain ⟨hpoint, hintegral⟩ := main
  have hcont : Continuous (iteratedDeriv k
      (fun y : ℝ => (I * (y : ℂ)) ^ diffOrder α * (Real.exp (-t * y ^ 2) : ℂ))) :=
    ((hpow k).mul (hgauss k)).continuous_iteratedDeriv k le_rfl
  have hfinite : ∫⁻ y : ℝ, ‖iteratedDeriv k
      (fun y : ℝ => (I * (y : ℂ)) ^ diffOrder α * (Real.exp (-t * y ^ 2) : ℂ)) y‖ₑ < ⊤ :=
    lt_of_le_of_lt hintegral (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hmomfin.lt_top) ENNReal.ofReal_lt_top)
  have hapos : 0 < 1 / 2 * heatDecay * t := by positivity
  have hKnonneg : 0 ≤ t ^ (((k : ℝ) - diffOrder α) / 2) := by positivity
  have hbound : ∀ y, ‖iteratedDeriv k
      (fun y : ℝ => (I * (y : ℂ)) ^ diffOrder α * (Real.exp (-t * y ^ 2) : ℂ)) y‖ₑ ≤
      ENNReal.ofReal symmetryConstant * binomialMoment k (diffOrder α) * ENNReal.ofReal
        (t ^ (((k : ℝ) - diffOrder α) / 2) * Real.exp (-(1 / 2 * heatDecay * t * y ^ 2))) := hpoint
  have htop : Tendsto (fun y : ℝ => y ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hbot : Tendsto (fun y : ℝ => y ^ 2) atBot atTop := by
    simpa [Function.comp_def] using htop.comp tendsto_neg_atBot_atTop
  exact ⟨hpoint, hintegral, ⟨hcont.aestronglyMeasurable, hfinite⟩,
    tendsto_zero_of_enorm_le hmomfin hKnonneg hsy.le (tendsto_exp_neg_mul_sq htop hapos) hbound,
    tendsto_zero_of_enorm_le hmomfin hKnonneg hsy.le (tendsto_exp_neg_mul_sq hbot hapos) hbound⟩
end YangMills.Construction.FreeKernel.MonomialGaussian
end
