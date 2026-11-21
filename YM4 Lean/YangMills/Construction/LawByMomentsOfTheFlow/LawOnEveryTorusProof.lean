import YangMills.Construction.LawByMomentsOfTheFlow.CumulantAtBoundedCouplings
import YangMills.Construction.LawByMomentsOfTheFlow.EnergyOfAChainHasACanonicalGaussian
import YangMills.Construction.LawByMomentsOfTheFlow.LawAtLargeCouplings
import YangMills.Construction.LawByMomentsOfTheFlow.LawOnEveryTorus
import YangMills.Construction.LawByMomentsOfTheFlow.TheFlowAboveTheWindow
import YangMills.Construction.LawByMomentsOfTheFlow.ValueOfTheFreeCumulant
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusLumps RenormalizationStepParameters LevelTestFunctions
theorem torusCumulant_bound (hA : largeCouplingCumulantStatement) (hB : cumulantBoundedCouplingStatement)
    (hV : freeCumulantValueStatement) (hW : CouplingFlowAboveWindow)
    (hG : levelEnergyCanonicalGaussianStatement) : torusCumulantStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, h₁⟩ := hA a ha
  obtain ⟨L₂, r₂, C₂, hr₂, h₂⟩ := hB a ha
  obtain ⟨L₃, r₃, C₃, hr₃, h₃⟩ := hV a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max C₁ (max C₂ C₃),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hCH hrt hC
  obtain ⟨M₁, f₁⟩ := h₁ L hodd ((le_max_left _ _).trans hL) Tb hTa hTL hD hCS hCH
    (hrt.trans (min_le_left _ _)) ((le_max_left _ _).trans hC)
  obtain ⟨M₂, f₂⟩ := h₂ L hodd (((le_max_left _ _).trans (le_max_right _ _)).trans hL) Tb hTa hTL hD hCS hCH
    (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (((le_max_left _ _).trans (le_max_right _ _)).trans hC)
  refine ⟨max M₁ M₂, fun Kr hM hη hN hKr hRet => ?_⟩
  obtain ⟨y₁, g₁⟩ := f₁ Kr ((le_max_left _ _).trans hM) hη hN hKr hRet
  obtain ⟨y₂, g₂⟩ := f₂ Kr ((le_max_right _ _).trans hM) hη hN hKr hRet
  obtain ⟨y₃, g₃⟩ := h₃ L hodd (((le_max_right _ _).trans (le_max_right _ _)).trans hL) Tb hTa hTL hD hCS hCH
    (hrt.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (((le_max_right _ _).trans (le_max_right _ _)).trans hC) Kr hKr
  refine ⟨max y₁ (max y₂ (max y₃ Tb.floorMin)), fun y hy hret hbot g hg hgy k _ hk2 hk8 R d hd => ?_⟩
  obtain ⟨A, c₁, X₁, -, hyX, hAS⟩ := g₁ y ((le_max_left _ _).trans hy) hret hbot g hg hgy k hk2 hk8 R d hd
  obtain ⟨B, c₂, X₂, -, -, hBS⟩ := g₂ y (((le_max_left _ _).trans (le_max_right _ _)).trans hy) hret hbot g hg hgy k
    hk2 hk8 R d hd
  obtain ⟨D, c₃, X₃, -, -, hDS⟩ := g₃ y
    (((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy) hret hbot g hg hgy k
    hk2 hk8 R d hd
  have hfit : (Tb.stepParameters y).Admissible :=
    hD.fits y (((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy)
  have hy1 : (1 : ℝ) ≤ y := hfit.y₁_ge
  have hX : 0 < X₁ := by linarith
  have hrun : AdmissibleStep (Tb.stepParameters y) := ⟨hfit, hret, hbot⟩
  refine ⟨fun _ => |A 0| + (X₁ ^ k * |B ⌈X₁⌉₊| + |D 0|) * X₁ ^ (1 / 10 : ℝ), 1, X₁, one_pos, hyX, fun S => ?_⟩
  obtain ⟨μ, hμ⟩ := hG _ (zero_le_one.trans hD.a_ge) (Tb.stepParameters y).side S.data.windowLevel
    (S.data.period (Tb.stepParameters y).side)
  have hγ : |S.latticeCycleSumAt S.data.scaleLevel| ≤ D 0 := (hDS S μ hμ).2.2.2.2.1
  have hxy : y ≤ S.scaleCoupling :=
    (hW _ hrun g hg hgy S.β S.data.windowLevel S.window_le S.passage).1 S.data.scaleLevel
      S.supAdmissible.scaleLevel_le
  have hx : 0 < S.scaleCoupling := by linarith
  have hrp : 0 ≤ S.scaleCoupling ^ (-(1 / 10) : ℝ) := Real.rpow_nonneg hx.le _
  have hT : 0 ≤ X₁ ^ k * |B ⌈X₁⌉₊| + |D 0| := by positivity
  have hXp : 0 ≤ X₁ ^ (1 / 10 : ℝ) := Real.rpow_nonneg hX.le _
  show ‖(S.scaleCoupling : ℂ) ^ k * S.torusCumulant - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤
    (|A 0| + (X₁ ^ k * |B ⌈X₁⌉₊| + |D 0|) * X₁ ^ (1 / 10 : ℝ)) * S.scaleCoupling ^ (-(1 / 10) : ℝ)
  rcases le_or_gt X₁ S.scaleCoupling with hbig | hsmall
  · refine (hAS S hbig).trans (mul_le_mul_of_nonneg_right ?_ hrp)
    have := le_abs_self (A 0)
    have := mul_nonneg hT hXp
    linarith
  · have hc : ‖S.torusCumulant‖ ≤ B ⌈X₁⌉₊ := hBS S _ (hsmall.le.trans (Nat.le_ceil _))
    have hpow : S.scaleCoupling ^ k ≤ X₁ ^ k := pow_le_pow_left₀ hx.le hsmall.le k
    have h1 : ‖(S.scaleCoupling : ℂ) ^ k * S.torusCumulant - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤
        X₁ ^ k * |B ⌈X₁⌉₊| + |D 0| := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.le]
        exact mul_le_mul hpow (hc.trans (le_abs_self _)) (norm_nonneg _) (by positivity)
      · rw [Complex.norm_real, Real.norm_eq_abs]
        exact hγ.trans (le_abs_self _)
    have h2 : X₁ ^ (-(1 / 10) : ℝ) ≤ S.scaleCoupling ^ (-(1 / 10) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hx hsmall.le (by norm_num)
    have h3 : X₁ ^ (1 / 10 : ℝ) * X₁ ^ (-(1 / 10) : ℝ) = 1 := by
      rw [← Real.rpow_add hX]
      norm_num
    have h4 : 1 ≤ X₁ ^ (1 / 10 : ℝ) * S.scaleCoupling ^ (-(1 / 10) : ℝ) :=
      h3.symm.le.trans (mul_le_mul_of_nonneg_left h2 hXp)
    have h5 : X₁ ^ k * |B ⌈X₁⌉₊| + |D 0| ≤
        (X₁ ^ k * |B ⌈X₁⌉₊| + |D 0|) * (X₁ ^ (1 / 10 : ℝ) * S.scaleCoupling ^ (-(1 / 10) : ℝ)) :=
      le_mul_of_one_le_right hT h4
    have h6 : 0 ≤ |A 0| * S.scaleCoupling ^ (-(1 / 10) : ℝ) := mul_nonneg (abs_nonneg _) hrp
    calc _ ≤ X₁ ^ k * |B ⌈X₁⌉₊| + |D 0| := h1
      _ ≤ (X₁ ^ k * |B ⌈X₁⌉₊| + |D 0|) * (X₁ ^ (1 / 10 : ℝ) * S.scaleCoupling ^ (-(1 / 10) : ℝ)) := h5
      _ ≤ _ := by nlinarith
end YangMills.Construction.MomentLaw
end
