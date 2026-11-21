import YangMills.Construction.FreeKernel.BoundFromABoundAndADecay
import YangMills.Construction.FreeKernel.LatticeGaussianPeriodEstimate
import YangMills.Construction.FreeKernel.LongTimeBoundOfTheDifferencesOfTheHeatKernel
import YangMills.Construction.FreeKernel.PeriodicIntegrationByParts
import YangMills.Construction.FreeKernel.SymbolsAddUpAndKernelsAsFourierIntegrals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.HeatKernelDiffLongTimeBoundProof
open Complex MeasureTheory YangMills.Construction.LatticeKernel
open YangMills.Construction.Constants.HeatKernel YangMills.Construction.FourDimKernel
open scoped ContDiff
lemma contDiff_laplacianSymbol : ContDiff ℝ ∞ laplacianSymbol := by apply _root_.YangMills.Construction.LatticeKernel.SymbolEstimates.contDiff_laplacianSymbol <;> assumption
lemma contDiff_exp_neg_mul_laplacianSymbol (t : ℝ) :
    ContDiff ℝ ∞ (fun x => Real.exp (-t * laplacianSymbol x)) := by
  have h := contDiff_laplacianSymbol
  fun_prop
lemma contDiff_ofReal_comp {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => (g x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hg
lemma contDiff_diffMultiplier (α : DiffKind) : ContDiff ℝ ∞ (diffMultiplier α) := by apply _root_.YangMills.Construction.FreeKernel.LatticeGaussianPeriod.contDiff_diffMultiplier <;> assumption
lemma periodic_laplacianSymbol : Function.Periodic laplacianSymbol (2 * Real.pi) := by
  intro θ
  simp [laplacianSymbol, Real.cos_add_two_pi]
lemma periodic_diffMultiplier (α : DiffKind) :
    Function.Periodic (diffMultiplier α) (2 * Real.pi) := by
  have hE : ∀ θ : ℝ, Complex.exp (I * ((θ + 2 * Real.pi : ℝ) : ℂ)) = Complex.exp (I * (θ : ℂ)) := by
    intro θ
    have : I * ((θ + 2 * Real.pi : ℝ) : ℂ) = I * (θ : ℂ) + 2 * Real.pi * I := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hE' : ∀ θ : ℝ,
      Complex.exp (-(I * ((θ + 2 * Real.pi : ℝ) : ℂ))) = Complex.exp (-(I * (θ : ℂ))) := by
    intro θ
    rw [Complex.exp_neg, Complex.exp_neg, hE]
  intro θ
  cases α with
  | identity => rfl
  | forward => simp only [diffMultiplier, hE]
  | backward => simp only [diffMultiplier, hE']
  | laplacian => simp only [diffMultiplier, periodic_laplacianSymbol θ]
lemma iteratedDeriv_ofReal_comp_real {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedDeriv k (fun x => (g x : ℂ)) = fun x => ((iteratedDeriv k g x : ℝ) : ℂ) := by apply _root_.YangMills.Construction.LatticeKernel.SymbolEstimates.iteratedDeriv_ofReal_comp <;> assumption
lemma iteratedDerivWithin_Icc_pi {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (k : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) :
    iteratedDerivWithin k g (Set.Icc (-Real.pi) Real.pi) θ = iteratedDeriv k g θ :=
  iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by linarith [Real.pi_pos]))
    ((hg.of_le (by exact_mod_cast le_top)).contDiffAt) hθ
lemma lintegral_enorm_iteratedDeriv_le
    (hω : ∀ θ : ℝ, homotopySymbol 1 θ = laplacianSymbol θ)
    (hOrd : SymbolVanishingOrders) (hExp : ExpSymbolDerivativeBounds)
    (hP : VanishingTimesGaussianBound) (m : ℕ) (α : DiffKind) {t : ℝ}
    (ht : 1 ≤ t) :
    ∫⁻ θ in Set.Icc (-Real.pi) Real.pi,
        ‖iteratedDeriv m
          (fun x : ℝ => diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ)) θ‖ₑ ≤
      ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant *
        binomialMoment m (diffOrder α) *
        ENNReal.ofReal (t ^ (((m : ℝ) - diffOrder α - 1) / 2)) := by
  have hCs : 0 ≤ symmetryConstant := by
    unfold symmetryConstant
    positivity
  have hρ := contDiff_diffMultiplier α
  have hf := contDiff_exp_neg_mul_laplacianSymbol t
  have he := contDiff_ofReal_comp hf
  have hσ : ContDiff ℝ ∞
      (fun x : ℝ => diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ)) :=
    hρ.mul he
  have hmain := (hP m (diffOrder α) symmetryConstant t (Set.Icc (-Real.pi) Real.pi)
    (diffMultiplier α)
    (fun x => ((Real.exp (-t * laplacianSymbol x) : ℝ) : ℂ)) hCs ht Set.ordConnected_Icc
    (hρ.of_le (by exact_mod_cast le_top)).contDiffOn
    (he.of_le (by exact_mod_cast le_top)).contDiffOn ?_).2
  · refine le_of_eq_of_le (setLIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_) hmain
    exact congrArg _ (iteratedDerivWithin_Icc_pi hσ m hθ).symm
  · intro k _ θ hθ
    refine ⟨?_, ?_⟩
    · rw [iteratedDerivWithin_Icc_pi hρ k hθ]
      exact ((hOrd.2.2 α k θ hθ).1)
    · rw [iteratedDerivWithin_Icc_pi he k hθ, iteratedDeriv_ofReal_comp_real hf]
      have hr : ExpSymbolRange t 1 θ :=
        Or.inl ⟨ht, zero_le_one, le_rfl, abs_le.mpr ⟨hθ.1, hθ.2⟩⟩
      obtain ⟨h1, h2⟩ := hExp k t 1 θ hr
      have hfun : (fun x => Real.exp (-t * homotopySymbol 1 x)) =
          fun x => Real.exp (-t * laplacianSymbol x) := by
        funext x
        rw [hω]
      rw [hfun] at h1
      refine le_trans ?_ h2
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal h1
lemma norm_integral_exp_mul_le {g : ℝ → ℂ} (hg : Continuous g) (j : ℤ) {B : ENNReal}
    (hB : B ≠ ⊤) (h : ∫⁻ θ in Set.Icc (-Real.pi) Real.pi, ‖g θ‖ₑ ≤ B) :
    ‖∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) * g θ‖ ≤ B.toReal := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  calc ‖∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) * g θ‖
      ≤ ∫ θ in (-Real.pi)..Real.pi, ‖Complex.exp (I * (j : ℂ) * (θ : ℂ)) * g θ‖ :=
        intervalIntegral.norm_integral_le_integral_norm hpi
    _ = ∫ θ in (-Real.pi)..Real.pi, ‖g θ‖ := by
        refine intervalIntegral.integral_congr fun θ _ => ?_
        have : I * (j : ℂ) * (θ : ℂ) = (((j : ℝ) * θ : ℝ) : ℂ) * I := by
          push_cast
          ring
        simp only [norm_mul, this, Complex.norm_exp_ofReal_mul_I, one_mul]
    _ = ∫ θ in Set.Icc (-Real.pi) Real.pi, ‖g θ‖ := by
        rw [intervalIntegral.integral_of_le hpi, integral_Icc_eq_integral_Ioc]
    _ = (∫⁻ θ in Set.Icc (-Real.pi) Real.pi, ‖g θ‖ₑ).toReal :=
        integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable
    _ ≤ B.toReal := ENNReal.toReal_mono hB h
lemma moment_le_derivativeMoment (m b : ℕ) :
    ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal symmetryConstant *
      binomialMoment m b ≤ derivativeMoment m b := by
  have hpi : 0 ≤ Real.pi ^ ((3 : ℝ) / 2) := by positivity
  unfold derivativeMoment
  rw [ENNReal.ofReal_mul hpi]
  gcongr
  calc binomialMoment m b ≤ 2 * binomialMoment m b := by
        rw [two_mul]
        exact le_self_add
    _ ≤ 2 * binomialMoment m b + binomialMoment m (b + 1) := le_self_add
    _ ≤ _ := le_self_add
lemma diffOrder_mem (α : DiffKind) : diffOrder α ∈ ({0, 1, 2} : Finset ℕ) := by
  cases α <;> simp [diffOrder]
lemma mul_derivativeMoment_le {n m : ℕ} (hB : kernelDerivativeBound n ≠ ⊤) (α : DiffKind)
    (hm : m = 0 ∨ m = n) :
    2 ^ n / (2 * Real.pi) * (derivativeMoment m (diffOrder α)).toReal ≤
      (kernelDerivativeBound n).toReal := by
  have hc : 0 ≤ (2 : ℝ) ^ n / (2 * Real.pi) := by positivity
  have hle : derivativeMoment m (diffOrder α) ≤
      ({0, 1, 2} : Finset ℕ).sup fun b => max (derivativeMoment 0 b) (derivativeMoment n b) := by
    refine le_trans ?_ (Finset.le_sup
      (f := fun b => max (derivativeMoment 0 b) (derivativeMoment n b)) (diffOrder_mem α))
    rcases hm with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hmul : ENNReal.ofReal (2 ^ n / (2 * Real.pi)) * derivativeMoment m (diffOrder α) ≤
      kernelDerivativeBound n := by
    unfold kernelDerivativeBound
    gcongr
  have h := ENNReal.toReal_mono hB hmul
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h
theorem heatKernelDiffLongTimeBound_holds (hF : symbolsAndFourierIntegrals)
    (hS : SymbolDerivativeBounds) (hP : VanishingTimesGaussianBound)
    (hN : finite_and_pos)
    (hI : PeriodicFourierIntegrationByParts) (hC : BoundFromBoundAndDecay) :
    HeatKernelDiffLongTimeBound := by
  intro n α t ht j
  obtain ⟨⟨-, -, -, hω, -⟩, hFourier⟩ := hF
  obtain ⟨-, -, -, hOrd, hExp⟩ := hS
  obtain ⟨-, -, -, -, -, -, -, -, hFin, hBfin, -⟩ := hN
  have ht0 : 0 < t := by linarith
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ → ℂ,
      σ = fun x : ℝ => diffMultiplier α x * (Real.exp (-t * laplacianSymbol x) : ℂ) := ⟨_, rfl⟩
  have hσc : ContDiff ℝ ∞ σ := by
    rw [hσdef]
    exact (contDiff_diffMultiplier α).mul
      (contDiff_ofReal_comp (contDiff_exp_neg_mul_laplacianSymbol t))
  have hσp : Function.Periodic σ (2 * Real.pi) := by
    intro θ
    rw [hσdef]
    simp only [periodic_diffMultiplier α θ, periodic_laplacianSymbol θ]
  have hmain : ∀ m : ℕ,
      ‖∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) * iteratedDeriv m σ θ‖ ≤
        (derivativeMoment m (diffOrder α)).toReal * t ^ (((m : ℝ) - diffOrder α - 1) / 2) := by
    intro m
    have h1 : ∫⁻ θ in Set.Icc (-Real.pi) Real.pi, ‖iteratedDeriv m σ θ‖ₑ ≤
        derivativeMoment m (diffOrder α) *
          ENNReal.ofReal (t ^ (((m : ℝ) - diffOrder α - 1) / 2)) := by
      rw [hσdef]
      refine (lintegral_enorm_iteratedDeriv_le hω hOrd hExp hP m α ht).trans ?_
      gcongr
      exact moment_le_derivativeMoment m (diffOrder α)
    have h2 := norm_integral_exp_mul_le
      (hσc.continuous_iteratedDeriv m (by exact_mod_cast le_top)) j
      (ENNReal.mul_ne_top (hFin m _).1 ENNReal.ofReal_ne_top) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  have hrep : diffOp α (discreteHeatKernel t) j = (((1 / (2 * Real.pi) : ℝ)) : ℂ) *
      ∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) * σ θ := by
    have hc : (1 / (2 * (Real.pi : ℂ))) = (((1 / (2 * Real.pi) : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [(hFourier t ht0 j 0 α).2.1, hσdef, hc]
    congr 1
    exact intervalIntegral.integral_congr fun θ _ => mul_assoc _ _ _
  have hnorm : ‖diffOp α (discreteHeatKernel t) j‖ = 1 / (2 * Real.pi) *
      ‖∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) * σ θ‖ := by
    rw [hrep, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  obtain ⟨tb, htb⟩ : ∃ tb : ℝ, tb = t ^ (((diffOrder α : ℝ) + 1) / 2) := ⟨_, rfl⟩
  have htb0 : 0 < tb := by
    rw [htb]
    positivity
  have hE : ∀ m : ℕ, t ^ (((m : ℝ) - diffOrder α - 1) / 2) * tb = Real.sqrt t ^ m := by
    intro m
    rw [htb, ← Real.rpow_add ht0, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    congr 1
    ring
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 1 / (2 * Real.pi) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = |(j : ℝ)| / Real.sqrt t := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by
    rw [hy]
    positivity
  have hX0 : ‖diffOp α (discreteHeatKernel t) j‖ * tb ≤
      P * (derivativeMoment 0 (diffOrder α)).toReal := by
    have h0 := hmain 0
    rw [iteratedDeriv_zero] at h0
    have h1 := hE 0
    rw [pow_zero] at h1
    calc ‖diffOp α (discreteHeatKernel t) j‖ * tb
        = P * ‖∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (j : ℂ) * (θ : ℂ)) * σ θ‖ * tb := by
          rw [hnorm, hPdef]
      _ ≤ P * ((derivativeMoment 0 (diffOrder α)).toReal *
            t ^ ((((0 : ℕ) : ℝ) - diffOrder α - 1) / 2)) * tb := by
          gcongr
      _ = P * (derivativeMoment 0 (diffOrder α)).toReal *
            (t ^ ((((0 : ℕ) : ℝ) - diffOrder α - 1) / 2) * tb) := by ring
      _ = P * (derivativeMoment 0 (diffOrder α)).toReal := by rw [h1, mul_one]
  have hXn : 0 < y → ‖diffOp α (discreteHeatKernel t) j‖ * tb ≤
      P * (derivativeMoment n (diffOrder α)).toReal * y ^ (-(n : ℝ)) := by
    intro hypos
    have hj : j ≠ 0 := by
      rintro rfl
      simp [hy] at hypos
    have hparts := hI n σ j hj (hσc.of_le (by exact_mod_cast le_top)) hσp
    have hpow : ‖(I / (j : ℂ)) ^ n‖ = (|(j : ℝ)|⁻¹) ^ n := by
      rw [norm_pow, norm_div, Complex.norm_I, Complex.norm_intCast, one_div]
    have hypow : y ^ (-(n : ℝ)) = (|(j : ℝ)|⁻¹) ^ n * Real.sqrt t ^ n := by
      rw [Real.rpow_neg hy0, Real.rpow_natCast, hy, div_pow, inv_div, inv_pow, div_eq_mul_inv,
        mul_comm]
    calc ‖diffOp α (discreteHeatKernel t) j‖ * tb
        = P * ((|(j : ℝ)|⁻¹) ^ n * ‖∫ θ in (-Real.pi)..Real.pi,
            Complex.exp (I * (j : ℂ) * (θ : ℂ)) * iteratedDeriv n σ θ‖) * tb := by
          rw [hnorm, hparts, norm_mul, hpow, hPdef]
      _ ≤ P * ((|(j : ℝ)|⁻¹) ^ n * ((derivativeMoment n (diffOrder α)).toReal *
            t ^ (((n : ℝ) - diffOrder α - 1) / 2))) * tb := by
          gcongr
          exact hmain n
      _ = P * (derivativeMoment n (diffOrder α)).toReal * ((|(j : ℝ)|⁻¹) ^ n *
            (t ^ (((n : ℝ) - diffOrder α - 1) / 2) * tb)) := by ring
      _ = P * (derivativeMoment n (diffOrder α)).toReal * y ^ (-(n : ℝ)) := by rw [hE n, hypow]
  have hcomb := hC n y (‖diffOp α (discreteHeatKernel t) j‖ * tb)
    (P * (derivativeMoment 0 (diffOrder α)).toReal)
    (P * (derivativeMoment n (diffOrder α)).toReal) hy0 (by positivity)
    (mul_nonneg hP0 ENNReal.toReal_nonneg) (mul_nonneg hP0 ENNReal.toReal_nonneg) hX0 hXn
  have hcB : (2 : ℝ) ^ n * max (P * (derivativeMoment 0 (diffOrder α)).toReal)
      (P * (derivativeMoment n (diffOrder α)).toReal) ≤ (kernelDerivativeBound n).toReal := by
    rw [mul_max_of_nonneg _ _ (by positivity)]
    refine max_le ?_ ?_
    · have h := mul_derivativeMoment_le (n := n) (m := 0) (hBfin n).1 α (Or.inl rfl)
      calc (2 : ℝ) ^ n * (P * (derivativeMoment 0 (diffOrder α)).toReal)
          = 2 ^ n / (2 * Real.pi) * (derivativeMoment 0 (diffOrder α)).toReal := by
            rw [hPdef]
            ring
        _ ≤ _ := h
    · have h := mul_derivativeMoment_le (n := n) (m := n) (hBfin n).1 α (Or.inr rfl)
      calc (2 : ℝ) ^ n * (P * (derivativeMoment n (diffOrder α)).toReal)
          = 2 ^ n / (2 * Real.pi) * (derivativeMoment n (diffOrder α)).toReal := by
            rw [hPdef]
            ring
        _ ≤ _ := h
  have hO : 0 ≤ bracketOnePlus y ^ (-(n : ℝ)) := by
    apply Real.rpow_nonneg
    unfold bracketOnePlus
    linarith
  rw [← hy, Real.rpow_neg ht0.le, ← htb]
  calc ‖diffOp α (discreteHeatKernel t) j‖
      = ‖diffOp α (discreteHeatKernel t) j‖ * tb * tb⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ htb0.ne', mul_one]
    _ ≤ 2 ^ n * max (P * (derivativeMoment 0 (diffOrder α)).toReal)
          (P * (derivativeMoment n (diffOrder α)).toReal) *
          bracketOnePlus y ^ (-(n : ℝ)) * tb⁻¹ := by
        gcongr
    _ ≤ (kernelDerivativeBound n).toReal * bracketOnePlus y ^ (-(n : ℝ)) * tb⁻¹ := by
        gcongr
    _ = (kernelDerivativeBound n).toReal * tb⁻¹ * bracketOnePlus y ^ (-(n : ℝ)) := by ring
end YangMills.Construction.FreeKernel.HeatKernelDiffLongTimeBoundProof
end
