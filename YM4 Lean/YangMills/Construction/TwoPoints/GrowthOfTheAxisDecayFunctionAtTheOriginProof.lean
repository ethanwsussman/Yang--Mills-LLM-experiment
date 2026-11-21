import YangMills.Construction.SpectralCalculus.FormCompletionAndBoundedExtension
import YangMills.Construction.TwoPoints.AveragingOverTheDilation
import YangMills.Construction.TwoPoints.GrowthOfTheAxisDecayFunctionAtTheOrigin
import YangMills.Construction.TwoPoints.OneFieldSpaceAndSlidesAlongTheNormal
import YangMills.Construction.TwoPoints.PartsOfATestPlate
import YangMills.Construction.TwoPoints.SpectralMeasuresVanishOutsideTheCone
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set YangMills.Construction.SpectralCalculus
open scoped NNReal ENNReal Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
namespace AxisDecayGrowthAtZero
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
open YangMills.Construction.Splines (cubicSpline cubicSplineIntegral)
open YangMills.Construction.TwoPoints.Shapes (timeBump shapeConst IsTimeBump)
open YangMills.Construction.TwoPoints.TestPlates (plateWidthNorm growthConst decayGrowthConst
  plateConst averageLowerConst weightSupConst timeLaplace scaledSplineFourier scaledFrequency
  planeBumpAt widthPlate upperCellPlate lowerCellPlate supportCells PlateHypotheses IsPlatePiece
  ReflectedPairAdmissible stripRect)
theorem bddAbove_expWeight :
    BddAbove ((fun x : ℝ => Real.exp (-x) * (1 + x ^ 2) ^ 4) '' Ici 0) := by
  refine ⟨(Nat.factorial 8 : ℝ) * Real.exp 1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx0 : (0 : ℝ) ≤ x := hx
  have h1 : (1 + x) ^ 8 / (Nat.factorial 8 : ℝ) ≤ Real.exp (1 + x) :=
    Real.pow_div_factorial_le_exp (1 + x) (by linarith) 8
  have hf : (0 : ℝ) < (Nat.factorial 8 : ℝ) := by positivity
  have h2 : (1 + x) ^ 8 ≤ (Nat.factorial 8 : ℝ) * Real.exp (1 + x) := by
    rw [div_le_iff₀ hf] at h1
    linarith
  have h3 : (1 + x ^ 2) ^ 4 ≤ (1 + x) ^ 8 := by
    have h4 : 1 + x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
    calc (1 + x ^ 2) ^ 4 ≤ ((1 + x) ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) h4 4
      _ = (1 + x) ^ 8 := by ring
  calc Real.exp (-x) * (1 + x ^ 2) ^ 4
      ≤ Real.exp (-x) * ((Nat.factorial 8 : ℝ) * Real.exp (1 + x)) :=
        mul_le_mul_of_nonneg_left (h3.trans h2) (Real.exp_pos _).le
    _ = (Nat.factorial 8 : ℝ) * Real.exp 1 := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
theorem expWeight_le_weightSupConst {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) * (1 + x ^ 2) ^ 4 ≤ weightSupConst :=
  le_csSup bddAbove_expWeight ⟨x, hx, rfl⟩
theorem weightSupConst_pos : 0 < weightSupConst := by
  have h := expWeight_le_weightSupConst (le_refl (0 : ℝ))
  norm_num at h
  linarith
theorem timeLaplace_lower_bound {ϖ E : ℝ} (hs : IsTimeBump timeBump) (hϖ : 0 < ϖ)
    (hE : 0 ≤ E) : 1 / 2 * ϖ * Real.exp (-(3 * ϖ * E)) ≤ timeLaplace ϖ E := by
  obtain ⟨hmem, hnn, -, hint⟩ := hs
  obtain ⟨⟨hc1, -, hsub⟩, -⟩ := hmem
  have hcont : Continuous timeBump := Complex.continuous_re.comp hc1.continuous
  have hzero : ∀ s, s ∉ Ioo (2 : ℝ) 3 → timeBump s = 0 := by
    intro s hs
    by_contra h
    apply hs
    apply hsub
    apply subset_tsupport
    simpa [Shapes.ofRealFun] using h
  set g : ℝ → ℝ := fun t => timeBump (t / ϖ) with hg
  have hgc : Continuous g := hcont.comp (continuous_id.div_const ϖ)
  have hgz : ∀ t, t ∉ Icc (2 * ϖ) (3 * ϖ) → g t = 0 := by
    intro t ht
    apply hzero
    intro h
    apply ht
    have h1 := h.1
    have h2 := h.2
    rw [lt_div_iff₀ hϖ] at h1
    rw [div_lt_iff₀ hϖ] at h2
    exact ⟨h1.le, h2.le⟩
  have hgs : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgz
  have i1 : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have i2 : Integrable fun t => g t * Real.exp (-(t * E)) :=
    (hgc.mul (by fun_prop)).integrable_of_hasCompactSupport hgs.mul_right
  have hI : ∫ t, g t = ϖ * ∫ s, timeBump s := by
    have h := Measure.integral_comp_div timeBump ϖ
    simpa [abs_of_pos hϖ] using h
  have hmain : (∫ t, g t * Real.exp (-(3 * ϖ * E))) ≤ ∫ t, g t * Real.exp (-(t * E)) := by
    refine integral_mono (i1.mul_const _) i2 fun t => ?_
    by_cases ht : t ∈ Icc (2 * ϖ) (3 * ϖ)
    · refine mul_le_mul_of_nonneg_left ?_ (hnn _)
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right ht.2 hE
      linarith
    · simp only [hgz t ht, zero_mul]
      exact le_refl _
  have h3 : 1 / 2 * ϖ * Real.exp (-(3 * ϖ * E)) ≤ ∫ t, g t * Real.exp (-(3 * ϖ * E)) := by
    rw [integral_mul_const, hI]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    nlinarith
  exact h3.trans hmain
theorem planeCoords_frame (t s : ℝ) :
    planeCoords (t • coordVec 3 + s • planePerp (coordVec 3)) = ![t, s] := by
  funext i
  fin_cases i <;>
    simp [planeCoords, planePerp, PeriodicLattice.coordVec]
theorem doubleLaplace_planeBump_eq (ϖ κ : ℝ) (p : SpectralPlane) :
    doubleLaplace (coordVec 3) (Shapes.ofRealFun (planeBumpAt ϖ κ)) p =
      (timeLaplace ϖ (p.1 : ℝ) : ℂ) * scaledSplineFourier ϖ κ p.2 := by
  have hin : ∀ t : ℝ,
      (∫ s : ℝ, Shapes.ofRealFun (planeBumpAt ϖ κ) ![t, s] *
        Complex.exp (((-t * (p.1 : ℝ) : ℝ) : ℂ) + Complex.I * ((s * p.2 : ℝ) : ℂ))) =
      ((timeBump (t / ϖ) * Real.exp (-(t * (p.1 : ℝ))) : ℝ) : ℂ) *
        scaledSplineFourier ϖ κ p.2 := by
    intro t
    rw [scaledSplineFourier, ← integral_const_mul]
    congr 1
    funext s
    have he : Complex.exp (((-t * (p.1 : ℝ) : ℝ) : ℂ)) =
        ((Real.exp (-(t * (p.1 : ℝ))) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 2
      ring
    simp only [Shapes.ofRealFun, planeBumpAt, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Complex.exp_add, he]
    push_cast
    ring_nf
  simp only [doubleLaplace, TwoPoints.lebesgueIntegral, integralWrt, planeCoords_frame, hin]
  rw [integral_mul_const, timeLaplace, integral_complex_ofReal]
def splineFourierFormula (ϖ κ q : ℝ) : ℝ :=
  1 / 4 * κ * ϖ * cubicSplineIntegral * Real.sinc (scaledFrequency ϖ κ q) ^ 4
def energyWeight (ϖ : ℝ) (p : SpectralPlane) : ℝ :=
  1 / 4 * ϖ ^ 2 * Real.exp (-(6 * ϖ * (p.1 : ℝ)))
theorem energyWeight_nonneg (ϖ : ℝ) (p : SpectralPlane) : 0 ≤ energyWeight ϖ p := by
  unfold energyWeight
  positivity
theorem energyWeight_mul_sq_le_enorm {ϖ κ : ℝ} (hs : IsTimeBump timeBump) (hϖ : 0 < ϖ)
    (hB : ∀ q, scaledSplineFourier ϖ κ q = (splineFourierFormula ϖ κ q : ℂ)) (p : SpectralPlane) :
    ENNReal.ofReal (energyWeight ϖ p * splineFourierFormula ϖ κ p.2 ^ 2) ≤
      ‖doubleLaplace (coordVec 3) (Shapes.ofRealFun (planeBumpAt ϖ κ)) p‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [doubleLaplace_planeBump_eq, hB, norm_mul, Complex.norm_real, Complex.norm_real, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hA := timeLaplace_lower_bound hs hϖ p.1.2
  have hpos : 0 ≤ 1 / 2 * ϖ * Real.exp (-(3 * ϖ * (p.1 : ℝ))) := by positivity
  have hsq := pow_le_pow_left₀ hpos hA 2
  refine le_trans (le_of_eq ?_) hsq
  have he : Real.exp (-(6 * ϖ * (p.1 : ℝ))) = Real.exp (-(3 * ϖ * (p.1 : ℝ))) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [energyWeight, he]
  ring
theorem continuous_splineFourierFormula (ϖ : ℝ) :
    Continuous fun x : ℝ × ℝ => splineFourierFormula ϖ x.1 x.2 := by
  unfold splineFourierFormula scaledFrequency
  refine (((continuous_const.mul continuous_fst).mul continuous_const).mul continuous_const).mul
    ((Real.continuous_sinc.comp ?_).pow 4)
  fun_prop
theorem measurable_weightedSplineSq (ϖ : ℝ) :
    Measurable fun x : ℝ × SpectralPlane =>
      ENNReal.ofReal (energyWeight ϖ x.2 * splineFourierFormula ϖ x.1 x.2.2 ^ 2) := by
  apply ENNReal.measurable_ofReal.comp
  apply Continuous.measurable
  have hE : Continuous fun x : ℝ × SpectralPlane => ((x.2.1 : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_fst.comp continuous_snd)
  have h1 : Continuous fun x : ℝ × SpectralPlane => energyWeight ϖ x.2 := by
    unfold energyWeight
    exact continuous_const.mul (Real.continuous_exp.comp ((continuous_const.mul hE).neg))
  have h2 : Continuous fun x : ℝ × SpectralPlane => splineFourierFormula ϖ x.1 x.2.2 :=
    (continuous_splineFourierFormula ϖ).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact h1.mul (h2.pow 2)
theorem measurable_energyDecay (t : ℝ) : Measurable (energyDecay t) :=
  Real.measurable_exp.comp (measurable_const.mul (measurable_coe_nnreal_real.comp measurable_fst))
theorem energyDecay_integral_le_of_bound {ρ : Measure SpectralPlane} [SFinite ρ]
    (hcone : ρ {p : SpectralPlane | (p.1 : ℝ) < |p.2|} = 0)
    (hav : DilationAveraging.Statement) {ϖ Bnd : ℝ} (hϖ : 0 < ϖ) (hB : 0 ≤ Bnd)
    (hbnd : ∀ κ ∈ Icc (1 : ℝ) 2,
      ∫⁻ p, ENNReal.ofReal (energyWeight ϖ p * splineFourierFormula ϖ κ p.2 ^ 2) ∂ρ ≤
        ENNReal.ofReal Bnd) :
    averageLowerConst * ϖ ^ 4 / (4 * weightSupConst) * ∫ p, energyDecay (7 * ϖ) p ∂ρ ≤ Bnd := by
  obtain ⟨hc', hav'⟩ := hav
  obtain ⟨hlow, hform, -, -⟩ := hav' ϖ hϖ
  have hC := weightSupConst_pos
  have hKpos : 0 < averageLowerConst * ϖ ^ 4 / (4 * weightSupConst) :=
    div_pos (mul_pos hc' (pow_pos hϖ 4)) (mul_pos four_pos hC)
  set K : ℝ := averageLowerConst * ϖ ^ 4 / (4 * weightSupConst) with hK
  set L : ℝ → SpectralPlane → ℝ≥0∞ := fun κ p =>
    ENNReal.ofReal (energyWeight ϖ p * splineFourierFormula ϖ κ p.2 ^ 2) with hL
  have hLm : Measurable (Function.uncurry L) := measurable_weightedSplineSq ϖ
  have h1 : ∫⁻ κ in Icc (1 : ℝ) 2, ∫⁻ p, L κ p ∂ρ ≤ ENNReal.ofReal Bnd := by
    calc ∫⁻ κ in Icc (1 : ℝ) 2, ∫⁻ p, L κ p ∂ρ
        ≤ ∫⁻ _ in Icc (1 : ℝ) 2, ENNReal.ofReal Bnd := setLIntegral_mono' measurableSet_Icc hbnd
      _ = ENNReal.ofReal Bnd := by
        rw [setLIntegral_const, Real.volume_Icc]
        norm_num
  have h2 : ∫⁻ κ in Icc (1 : ℝ) 2, ∫⁻ p, L κ p ∂ρ = ∫⁻ p, (∫⁻ κ in Icc (1 : ℝ) 2, L κ p) ∂ρ :=
    lintegral_lintegral_swap hLm.aemeasurable
  have h3 : ∀ᵐ p ∂ρ, ENNReal.ofReal (K * energyDecay (7 * ϖ) p) ≤
      ∫⁻ κ in Icc (1 : ℝ) 2, L κ p := by
    have hae : ∀ᵐ p ∂ρ, ¬ (p.1 : ℝ) < |p.2| := by
      rw [ae_iff]
      simp only [not_not]
      exact hcone
    filter_upwards [hae] with p hp
    have hp' : |p.2| ≤ (p.1 : ℝ) := not_lt.mp hp
    have hw := energyWeight_nonneg ϖ p
    have hcontκ : Continuous fun κ : ℝ => energyWeight ϖ p * splineFourierFormula ϖ κ p.2 ^ 2 :=
      continuous_const.mul (((continuous_splineFourierFormula ϖ).comp
        (continuous_id.prodMk continuous_const)).pow 2)
    have hE : ∫⁻ κ in Icc (1 : ℝ) 2, L κ p = ENNReal.ofReal
        (∫ κ in Icc (1 : ℝ) 2, energyWeight ϖ p * splineFourierFormula ϖ κ p.2 ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal hcontκ.integrableOn_Icc
        (Eventually.of_forall fun κ => mul_nonneg hw (sq_nonneg _))).symm
    rw [hE]
    apply ENNReal.ofReal_le_ofReal
    have hJ' : (∫ κ in (1 : ℝ)..2, splineFourierFormula ϖ κ p.2 ^ 2) =
        ∫ κ in (1 : ℝ)..2, (scaledSplineFourier ϖ κ p.2).re ^ 2 := by
      apply intervalIntegral.integral_congr
      intro κ hκ
      rw [uIcc_of_le one_le_two] at hκ
      show splineFourierFormula ϖ κ p.2 ^ 2 = (scaledSplineFourier ϖ κ p.2).re ^ 2
      rw [hform p.2 κ hκ, Complex.ofReal_re]
      rfl
    have hJ : (∫ κ in Icc (1 : ℝ) 2, energyWeight ϖ p * splineFourierFormula ϖ κ p.2 ^ 2) =
        energyWeight ϖ p * ∫ κ in (1 : ℝ)..2, (scaledSplineFourier ϖ κ p.2).re ^ 2 := by
      rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le one_le_two, hJ']
    rw [hJ]
    have hq := hlow p.2
    have hx0 : 0 ≤ ϖ * (p.1 : ℝ) := mul_nonneg hϖ.le p.1.2
    have hD0 : 0 < (1 + ϖ ^ 2 * p.2 ^ 2) ^ 4 := by positivity
    have hqx : ϖ ^ 2 * p.2 ^ 2 ≤ (ϖ * (p.1 : ℝ)) ^ 2 := by
      have h : p.2 ^ 2 ≤ (p.1 : ℝ) ^ 2 := by
        rw [← sq_abs p.2]
        exact pow_le_pow_left₀ (abs_nonneg _) hp' 2
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
    have hD : Real.exp (-(ϖ * (p.1 : ℝ))) * (1 + ϖ ^ 2 * p.2 ^ 2) ^ 4 ≤ weightSupConst :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 4)
        (Real.exp_pos _).le).trans (expWeight_le_weightSupConst hx0)
    have hinv : Real.exp (-(ϖ * (p.1 : ℝ))) / weightSupConst ≤
        (1 + ϖ ^ 2 * p.2 ^ 2) ^ (-4 : ℤ) := by
      have hz : (1 + ϖ ^ 2 * p.2 ^ 2) ^ (-4 : ℤ) = ((1 + ϖ ^ 2 * p.2 ^ 2) ^ 4)⁻¹ := by
        rw [zpow_neg]
        norm_cast
      rw [hz, div_le_iff₀ hC, inv_mul_eq_div, le_div_iff₀ hD0]
      exact hD
    have he : energyDecay (7 * ϖ) p =
        Real.exp (-(6 * ϖ * (p.1 : ℝ))) * Real.exp (-(ϖ * (p.1 : ℝ))) := by
      rw [energyDecay, ← Real.exp_add]
      congr 1
      ring
    calc K * energyDecay (7 * ϖ) p
        = energyWeight ϖ p *
            (averageLowerConst * ϖ ^ 2 * (Real.exp (-(ϖ * (p.1 : ℝ))) / weightSupConst)) := by
          rw [he, hK, energyWeight]
          field_simp
      _ ≤ energyWeight ϖ p * (averageLowerConst * ϖ ^ 2 * (1 + ϖ ^ 2 * p.2 ^ 2) ^ (-4 : ℤ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinv (mul_nonneg hc'.le (sq_nonneg _))) hw
      _ ≤ energyWeight ϖ p * ∫ κ in (1 : ℝ)..2, (scaledSplineFourier ϖ κ p.2).re ^ 2 :=
          mul_le_mul_of_nonneg_left hq hw
  have h4 : ∫⁻ p, ENNReal.ofReal (K * energyDecay (7 * ϖ) p) ∂ρ ≤ ENNReal.ofReal Bnd :=
    (lintegral_mono_ae h3).trans (h2 ▸ h1)
  have hm : Measurable fun p : SpectralPlane => K * energyDecay (7 * ϖ) p :=
    (measurable_energyDecay _).const_mul K
  have h5 : ∫ p, K * energyDecay (7 * ϖ) p ∂ρ =
      (∫⁻ p, ENNReal.ofReal (K * energyDecay (7 * ϖ) p) ∂ρ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun p => mul_nonneg hKpos.le (Real.exp_pos _).le)
      hm.aestronglyMeasurable
  rw [← integral_const_mul, h5]
  exact ENNReal.toReal_le_of_le_ofReal hB h4
section Classes
variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : V → V → ℂ}
theorem norm_constClass_sum_sub_le (hlin : IsLinearMap ℂ (constClass b)) {ι : Type*}
    (J : Finset ι) (up lo : ι → V) {c : ℝ} (hup : ∀ i ∈ J, ‖constClass b (up i)‖ ≤ c)
    (hlo : ∀ i ∈ J, ‖constClass b (lo i)‖ ≤ c) :
    ‖constClass b (∑ i ∈ J, (up i - lo i))‖ ≤ J.card * (2 * c) := by
  let Lc : V →ₗ[ℂ] SeparatedCompletion b := hlin.mk' _
  have hL : ∀ v, Lc v = constClass b v := fun _ => rfl
  have hmap : constClass b (∑ i ∈ J, (up i - lo i)) =
      ∑ i ∈ J, (constClass b (up i) - constClass b (lo i)) := by
    rw [← hL, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, hL, hL]
  rw [hmap]
  calc ‖∑ i ∈ J, (constClass b (up i) - constClass b (lo i))‖
      ≤ ∑ i ∈ J, ‖constClass b (up i) - constClass b (lo i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ J, 2 * c := Finset.sum_le_sum fun i hi =>
        (norm_sub_le _ _).trans (by linarith [hup i hi, hlo i hi])
    _ = J.card * (2 * c) := by simp
end Classes
theorem euclidDot_coordVec_three (x : AmbientSpace) :
    euclidDot (coordVec 3) x = x 3 := by
  simp [euclidDot, Fin.sum_univ_four, PeriodicLattice.coordVec]
theorem mem_halfSpaceDomain_of_isPlatePiece {ϖ : ℝ} {h : AmbientSpace → ℂ} (hϖ : 0 < ϖ)
    (hp : IsPlatePiece ϖ h) : h ∈ halfSpaceDomain (coordVec 3) := by
  refine ⟨hp.2.1.1.1, hp.2.1.1.2.1, fun x hx => ?_⟩
  have h2 := (hp.2.2 hx).1
  show 0 < euclidDot (coordVec 3) x
  rw [euclidDot_coordVec_three]
  linarith
theorem uniformNorm_ofRealFun (f : AmbientSpace → ℝ) :
    TestFunctions.uniformNorm (ofRealFun f) = TestFunctions.uniformNorm f := by
  simp [TestFunctions.uniformNorm, ofRealFun]
theorem norm_reflectedClass_sq {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hS : IsDisjointForm S)
    (hCF : SeparatedCompletionBasics (reflectedForm S (coordVec 3)))
    {h : AmbientSpace → ℂ} (hd : h ∈ halfSpaceDomain (coordVec 3)) (hh : h ∈ compactC1Real)
    (hθ : reflectFun (coordVec 3) h ∈ compactC1Real) :
    ‖reflectedClass S (coordVec 3) ⟨h, hd⟩‖ ^ 2 =
      S (reflectFun (coordVec 3) h) h := by
  have hconj : conjFun h = h := by
    funext x
    exact Complex.conj_eq_iff_im.mpr (hh.2 x)
  have h1 := hCF.inner_constClass ⟨h, hd⟩ ⟨h, hd⟩
  have h2 : reflectedForm S (coordVec 3) ⟨h, hd⟩ ⟨h, hd⟩ =
      (S (reflectFun (coordVec 3) h) h : ℂ) := by
    show complexifyForm S (reflectFun (coordVec 3) (conjFun h)) h = _
    rw [hconj]
    exact hS.complexifyForm_of_mem_compactC1Real hθ hh
  rw [h2] at h1
  have h3 := inner_self_eq_norm_sq (𝕜 := ℂ) (constClass (reflectedForm S (coordVec 3)) ⟨h, hd⟩)
  rw [h1] at h3
  show ‖constClass (reflectedForm S (coordVec 3)) ⟨h, hd⟩‖ ^ 2 = _
  rw [← h3]
  simp
theorem norm_reflectedClass_le {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    {d₀ ϖ W : ℝ} {u : ℝ → ℝ}
    (hS : IsDisjointForm S) (hP3 : IsSmallPositiveWith S shapeConst d₀ u)
    (hCF : SeparatedCompletionBasics (reflectedForm S (coordVec 3)))
    (hϖ : 0 < ϖ) (hd : 5 / 2 * ϖ ≤ d₀) {h : AmbientSpace → ℂ}
    (hdom : h ∈ halfSpaceDomain (coordVec 3))
    (hmir : ReflectedPairAdmissible ϖ h) (hW : 0 ≤ W)
    (hsup : TestFunctions.uniformNorm h ≤ 3 * W) :
    ‖reflectedClass S (coordVec 3) ⟨h, hdom⟩‖ ≤
      3 * W * Real.sqrt (u (5 / 2 * ϖ)) := by
  obtain ⟨⟨p, hp, h1, h2⟩, hθ, hh, hsn⟩ := hmir
  have hd' : 5 / 2 * ϖ ∈ Ioc 0 d₀ := ⟨by positivity, hd⟩
  have hu := hP3.rate_pos _ hd'
  have hb := hP3.le_rate _ hd' p hp (h1 ▸ hθ) (h2 ▸ hh)
  have hs1 : TestFunctions.uniformNorm p.1 = TestFunctions.uniformNorm h := by
    rw [← uniformNorm_ofRealFun, h1, hsn]
  have hs2 : TestFunctions.uniformNorm p.2 = TestFunctions.uniformNorm h := by
    rw [← uniformNorm_ofRealFun, h2]
  rw [h1, h2, hs1, hs2] at hb
  have hs0 : 0 ≤ TestFunctions.uniformNorm h := Real.iSup_nonneg fun _ => norm_nonneg _
  have hsq : ‖reflectedClass S (coordVec 3) ⟨h, hdom⟩‖ ^ 2 ≤
      (3 * W * Real.sqrt (u (5 / 2 * ϖ))) ^ 2 := by
    rw [norm_reflectedClass_sq hS hCF hdom hh hθ, mul_pow, Real.sq_sqrt hu.le]
    have h3 : TestFunctions.uniformNorm h * TestFunctions.uniformNorm h ≤ (3 * W) ^ 2 := by
      nlinarith
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
theorem planeBump_mem_cc1In {ϖ κ : ℝ} (hϖ : 0 < ϖ)
    (hshape : TestPlates.PlaneBumpProperties ϖ κ) :
    Shapes.ofRealFun (planeBumpAt ϖ κ) ∈ cc1In (positiveHalfPlane (coordVec 3)) := by
  obtain ⟨-, ⟨⟨hc, hk, -⟩, -⟩, -, hrect, -⟩ := hshape
  refine ⟨hc, hk, fun y hy => ?_⟩
  have hsub : tsupport (Shapes.ofRealFun (planeBumpAt ϖ κ)) ⊆ tsupport (planeBumpAt ϖ κ) := by
    refine closure_mono fun z hz h0 => hz ?_
    simp [Shapes.ofRealFun, h0]
  have h2 := (hrect (hsub hy)).1.1
  show 0 < euclidDot (planeCoords (coordVec 3)) y
  have hp : euclidDot (planeCoords (coordVec 3)) y = y 0 := by
    simp [euclidDot, Fin.sum_univ_two, planeCoords, PeriodicLattice.coordVec]
  rw [hp]
  linarith
theorem axisDecayTransform_le (hMeas : SpectralMeasuresAtAllNormals.Statement)
    (hCone : SpectralSupportInCone.Statement)
    (hAv : DilationAveraging.Statement)
    (hParts : TestPlates.TestPlatePieces.Statement)
    (hField : ReflectedSpaceAndSlides.Statement)
    (hCS : FormCompletionAndBoundedExtension)
    (hShapes : Shapes.ShapesExist.Statement)
    {St : FixedScale} {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {d₀ : ℝ} {u : ℝ → ℝ}
    {φ : (Fin 2 → ℝ) → ℂ} {r₁ : ℝ} (hForm : IsDisjointForm S) (h3 : IsAdmissibleForm St S)
    (hP3 : IsSmallPositiveWith S shapeConst d₀ u) (hφ : φ ∈ transProfiles)
    (hφ0 : φ ≠ 0) (hr : 0 < r₁) (hsupp : tsupport φ ⊆ {ζ | euclidNorm ζ ≤ r₁})
    {ϖ : ℝ} (h0 : 0 < ϖ) (hle : ϖ ≤ min 1 (min r₁ (2 / 5 * d₀))) :
    axisDecayTransform S φ (7 * ϖ) ≤
      growthConst * r₁ ^ 4 * plateWidthNorm ϖ φ ^ 2 * ϖ ^ (-8 : ℤ) * u (5 / 2 * ϖ) := by
  have hϖ1 : ϖ ≤ r₁ := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hϖd : ϖ ≤ 2 / 5 * d₀ := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd : 5 / 2 * ϖ ≤ d₀ := by linarith
  obtain ⟨hframe, -, -⟩ := hMeas St S φ hForm h3 hφ
  have hnormal := coordVec_three_mem_planeReflectionNormals
  have hfr := hframe _ hnormal
  have fam : IsSpectralFamily S φ (fun m => averagedKernelSpectralMeasure S φ m) :=
    ⟨fun m => (hframe m m.2).represents, fun m => (hframe m m.2).plateNorm⟩
  have hc : averagedKernelSpectralMeasure S φ (coordVec 3)
      {p : SpectralPlane | (p.1 : ℝ) < |p.2|} = 0 :=
    hCone St S φ _ hForm h3 hφ fam ⟨_, hnormal⟩
  obtain ⟨C₂, hC₂⟩ := h3.ballDecay
  have hb := (hField St S C₂ (coordVec 3) ⟨hForm, hnormal.1, h3⟩
    hC₂).1.1.posHermitian
  obtain ⟨-, hCF, -⟩ := hCS.1 _ _ hb
  have := hfr.sigmaFinite
  have hsh := hShapes.2.1
  have hne : ∃ ζ, φ ζ ≠ 0 := Function.ne_iff.mp hφ0
  have hu : 0 < u (5 / 2 * ϖ) := hP3.rate_pos _ ⟨by positivity, hd⟩
  obtain ⟨⟨-, -, -, hcard, hcount⟩, ⟨hWpos, -⟩, -⟩ :=
    hParts φ r₁ ϖ 1 ⟨hφ, hne, hr, hsupp, h0, hϖ1, by simp⟩
  have hbnd : ∀ κ ∈ Icc (1 : ℝ) 2,
      ∫⁻ p, ENNReal.ofReal (energyWeight ϖ p * splineFourierFormula ϖ κ p.2 ^ 2)
        ∂(averagedKernelSpectralMeasure S φ (coordVec 3)) ≤
      ENNReal.ofReal ((((supportCells ϖ φ).ncard : ℝ) *
        (2 * (3 * plateWidthNorm ϖ φ * Real.sqrt (u (5 / 2 * ϖ))))) ^ 2) := by
    intro κ hκ
    obtain ⟨⟨-, -, hfin, -, -⟩, -, hshape, ⟨hfmem, hfsum, hparts⟩, hmirror⟩ :=
      hParts φ r₁ ϖ κ ⟨hφ, hne, hr, hsupp, h0, hϖ1, hκ⟩
    have hα := planeBump_mem_cc1In h0 hshape
    have hdom : tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) φ ∈
        halfSpaceDomain (coordVec 3) := by
      refine ⟨hfmem.1.1, hfmem.1.2.1, fun x hx => ?_⟩
      have h2 : 0 < x 3 := hfmem.1.2.2 hx
      show 0 < euclidDot (coordVec 3) x
      rw [euclidDot_coordVec_three]
      exact h2
    have hB : ∀ q, scaledSplineFourier ϖ κ q = (splineFourierFormula ϖ κ q : ℂ) :=
      fun q => (hAv.2 ϖ h0).2.1 q κ hκ
    have hnorm := hfr.plateNorm _ hα hdom
    classical
    let up : (Fin 2 → ℤ) → halfSpaceDomain (coordVec 3) := fun ι =>
      if h : ι ∈ supportCells ϖ φ then
        ⟨upperCellPlate ϖ κ φ ι, mem_halfSpaceDomain_of_isPlatePiece h0 (hparts ι h).1⟩ else 0
    let lo : (Fin 2 → ℤ) → halfSpaceDomain (coordVec 3) := fun ι =>
      if h : ι ∈ supportCells ϖ φ then
        ⟨TestPlates.lowerCellPlate ϖ κ φ ι,
          mem_halfSpaceDomain_of_isPlatePiece h0 (hparts ι h).2.1⟩ else 0
    have hsumEq : (⟨tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) φ, hdom⟩ :
        halfSpaceDomain (coordVec 3)) = ∑ ι ∈ hfin.toFinset, (up ι - lo ι) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      show widthPlate ϖ κ φ = _
      rw [hfsum, finsum_mem_eq_finite_toFinset_sum _ hfin]
      refine Finset.sum_congr rfl fun ι hι => ?_
      have hm : ι ∈ supportCells ϖ φ := hfin.mem_toFinset.mp hι
      simp [up, lo, hm]
    have hcls : ‖reflectedClass S (coordVec 3)
        ⟨tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) φ, hdom⟩‖ ≤
        ((supportCells ϖ φ).ncard : ℝ) *
          (2 * (3 * plateWidthNorm ϖ φ * Real.sqrt (u (5 / 2 * ϖ)))) := by
      rw [Set.ncard_eq_toFinset_card _ hfin]
      show ‖constClass (reflectedForm S (coordVec 3)) _‖ ≤ _
      rw [hsumEq]
      refine norm_constClass_sum_sub_le hCF.isLinearMap_constClass _ up lo
        (fun ι hι => ?_) (fun ι hι => ?_)
      · have hm : ι ∈ supportCells ϖ φ := hfin.mem_toFinset.mp hι
        have he : up ι = ⟨upperCellPlate ϖ κ φ ι,
            mem_halfSpaceDomain_of_isPlatePiece h0 (hparts ι hm).1⟩ :=
          dif_pos hm
        rw [he]
        exact norm_reflectedClass_le hForm hP3 hCF h0 hd _ (hmirror ι hm).1 hWpos.le
          (hparts ι hm).2.2.2.2
      · have hm : ι ∈ supportCells ϖ φ := hfin.mem_toFinset.mp hι
        have he : lo ι = ⟨TestPlates.lowerCellPlate ϖ κ φ ι,
            mem_halfSpaceDomain_of_isPlatePiece h0 (hparts ι hm).2.1⟩ := dif_pos hm
        rw [he]
        refine norm_reflectedClass_le hForm hP3 hCF h0 hd _ (hmirror ι hm).2 hWpos.le ?_
        rw [(hparts ι hm).2.2.1]
        linarith
    calc ∫⁻ p, ENNReal.ofReal (energyWeight ϖ p * splineFourierFormula ϖ κ p.2 ^ 2)
          ∂(averagedKernelSpectralMeasure S φ (coordVec 3))
        ≤ ∫⁻ p, ‖doubleLaplace (coordVec 3) (Shapes.ofRealFun (planeBumpAt ϖ κ)) p‖ₑ ^ 2
          ∂(averagedKernelSpectralMeasure S φ (coordVec 3)) :=
          lintegral_mono fun p => energyWeight_mul_sq_le_enorm hsh h0 hB p
      _ = ENNReal.ofReal (‖reflectedClass S (coordVec 3)
          ⟨tensorPlate (Shapes.ofRealFun (planeBumpAt ϖ κ)) φ, hdom⟩‖ ^ 2) := hnorm.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hcls 2)
  have hdec := energyDecay_integral_le_of_bound hc hAv h0 (sq_nonneg _) hbnd
  have hΓ : axisDecayTransform S φ (7 * ϖ) =
      ∫ p, energyDecay (7 * ϖ) p ∂(averagedKernelSpectralMeasure S φ (coordVec 3)) := rfl
  rw [← hΓ] at hdec
  have hc' := hAv.1
  have hC := weightSupConst_pos
  have hKpos : 0 < averageLowerConst * ϖ ^ 4 / (4 * weightSupConst) :=
    div_pos (mul_pos hc' (pow_pos h0 4)) (mul_pos four_pos hC)
  have hv2 : Real.sqrt (u (5 / 2 * ϖ)) ^ 2 = u (5 / 2 * ϖ) := Real.sq_sqrt hu.le
  have hn0 : (0 : ℝ) ≤ ((supportCells ϖ φ).ncard : ℝ) := Nat.cast_nonneg _
  have hn2 : ((supportCells ϖ φ).ncard : ℝ) ^ 2 ≤ (25 * r₁ ^ 2 / ϖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ hn0 (hcard.trans hcount) 2
  have hB : (((supportCells ϖ φ).ncard : ℝ) *
      (2 * (3 * plateWidthNorm ϖ φ * Real.sqrt (u (5 / 2 * ϖ))))) ^ 2 ≤
      36 * (25 * r₁ ^ 2 / ϖ ^ 2) ^ 2 * plateWidthNorm ϖ φ ^ 2 * u (5 / 2 * ϖ) := by
    have he : (((supportCells ϖ φ).ncard : ℝ) *
        (2 * (3 * plateWidthNorm ϖ φ * Real.sqrt (u (5 / 2 * ϖ))))) ^ 2 =
        36 * ((supportCells ϖ φ).ncard : ℝ) ^ 2 * plateWidthNorm ϖ φ ^ 2 *
          Real.sqrt (u (5 / 2 * ϖ)) ^ 2 := by ring
    rw [he, hv2]
    gcongr
  have hfin : axisDecayTransform S φ (7 * ϖ) ≤
      (averageLowerConst * ϖ ^ 4 / (4 * weightSupConst))⁻¹ *
        (36 * (25 * r₁ ^ 2 / ϖ ^ 2) ^ 2 * plateWidthNorm ϖ φ ^ 2 * u (5 / 2 * ϖ)) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hKpos]
    linarith
  refine hfin.trans (le_of_eq ?_)
  have hz : ϖ ^ (-8 : ℤ) = (ϖ ^ 8)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  rw [growthConst, plateConst, hz]
  field_simp
  ring
end AxisDecayGrowthAtZero
theorem AxisDecayGrowthAtZero.holds
    (hMeas : SpectralMeasuresAtAllNormals.Statement)
    (hCone : SpectralSupportInCone.Statement)
    (hAv : DilationAveraging.Statement)
    (hParts : TestPlates.TestPlatePieces.Statement)
    (hField : ReflectedSpaceAndSlides.Statement)
    (hCS : FormCompletionAndBoundedExtension)
    (hShapes : Shapes.ShapesExist.Statement) :
    AxisDecayGrowthAtZero.Statement := by
  intro St S d₀ u φ r₁ hForm h3 hP3 hφ hφ0 hr hsupp
  have hbound : ∀ ϖ : ℝ, 0 < ϖ → ϖ ≤ min 1 (min r₁ (2 / 5 * d₀)) →
      axisDecayTransform S φ (7 * ϖ) ≤
        TestPlates.growthConst * r₁ ^ 4 * TestPlates.plateWidthNorm ϖ φ ^ 2 * ϖ ^ (-8 : ℤ) *
          u (5 / 2 * ϖ) := fun ϖ h0 hle =>
    AxisDecayGrowthAtZero.axisDecayTransform_le hMeas hCone hAv hParts hField hCS hShapes
      hForm h3 hP3 hφ hφ0 hr hsupp h0 hle
  have hd₀ := hP3.radius_pos
  have hmin : 0 < min 1 (min r₁ (2 / 5 * d₀)) :=
    lt_min one_pos (lt_min hr (by positivity))
  have hA : 0 ≤ TestFunctions.uniformNorm φ := Real.iSup_nonneg fun _ => norm_nonneg _
  have hG : 0 ≤ gradPlaneSup φ := ENNReal.toReal_nonneg
  have hgN : 0 ≤ TestPlates.growthConst := by
    have hc' := hAv.1
    have hC := AxisDecayGrowthAtZero.weightSupConst_pos
    rw [TestPlates.growthConst, TestPlates.plateConst]
    positivity
  have hstep : ∀ t : ℝ, 0 < t → t ≤ 7 * min 1 (min r₁ (2 / 5 * d₀)) →
      t ^ 8 * axisDecayTransform S φ t ≤
        TestPlates.decayGrowthConst * r₁ ^ 4 *
          (TestFunctions.uniformNorm φ + gradPlaneSup φ) ^ 2 * u (5 / 14 * t) := by
    intro t ht htle
    have hϖle : t / 7 ≤ min 1 (min r₁ (2 / 5 * d₀)) := by linarith
    have hϖ1 : t / 7 ≤ 1 := hϖle.trans (min_le_left _ _)
    have hϖd : t / 7 ≤ 2 / 5 * d₀ :=
      hϖle.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hΓ := hbound (t / 7) (by positivity) hϖle
    have e1 : 7 * (t / 7) = t := by ring
    have e2 : 5 / 2 * (t / 7) = 5 / 14 * t := by ring
    rw [e1, e2] at hΓ
    have hu : 0 < u (5 / 14 * t) := hP3.rate_pos _ ⟨by positivity, by linarith⟩
    have hW0 : 0 ≤ TestPlates.plateWidthNorm (t / 7) φ :=
      add_nonneg hA (mul_nonneg (by positivity) hG)
    have hW1 : TestPlates.plateWidthNorm (t / 7) φ ≤
        TestFunctions.uniformNorm φ + gradPlaneSup φ := by
      have := mul_le_mul_of_nonneg_right hϖ1 hG
      unfold TestPlates.plateWidthNorm
      linarith
    have h8 : (t / 7) ^ (-8 : ℤ) = ((t / 7) ^ 8)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    calc t ^ 8 * axisDecayTransform S φ t
        ≤ t ^ 8 * (TestPlates.growthConst * r₁ ^ 4 * TestPlates.plateWidthNorm (t / 7) φ ^ 2 *
            (t / 7) ^ (-8 : ℤ) * u (5 / 14 * t)) :=
          mul_le_mul_of_nonneg_left hΓ (by positivity)
      _ = 7 ^ 8 * TestPlates.growthConst * r₁ ^ 4 * TestPlates.plateWidthNorm (t / 7) φ ^ 2 *
            u (5 / 14 * t) := by
          rw [h8]
          field_simp
      _ ≤ 7 ^ 8 * TestPlates.growthConst * r₁ ^ 4 *
            (TestFunctions.uniformNorm φ + gradPlaneSup φ) ^ 2 * u (5 / 14 * t) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hW1 2)
              (mul_nonneg (mul_nonneg (by norm_num) hgN) (by positivity))) hu.le
      _ = TestPlates.decayGrowthConst * r₁ ^ 4 *
            (TestFunctions.uniformNorm φ + gradPlaneSup φ) ^ 2 * u (5 / 14 * t) := by
          rw [TestPlates.decayGrowthConst]
  have hframe := (hMeas St S φ hForm h3 hφ).1 _ coordVec_three_mem_planeReflectionNormals
  refine ⟨hbound, hstep, ?_⟩
  have hbpos : 0 < 7 * min 1 (min r₁ (2 / 5 * d₀)) := mul_pos (by norm_num) hmin
  have hlim : Tendsto (fun t : ℝ => 5 / 14 * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun t : ℝ => 5 / 14 * t) (𝓝 0) (𝓝 (5 / 14 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos (by norm_num : (0 : ℝ) < 5 / 14) ht
  have hg := (hP3.rate_tendsto.comp hlim).const_mul (TestPlates.decayGrowthConst * r₁ ^ 4 *
    (TestFunctions.uniformNorm φ + gradPlaneSup φ) ^ 2)
  rw [mul_zero] at hg
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [Ioo_mem_nhdsGT hbpos] with t ht
    exact mul_nonneg (pow_nonneg ht.1.le 8) (hframe.transform_nonneg t ht.1)
  · filter_upwards [Ioo_mem_nhdsGT hbpos] with t ht
    exact hstep t ht.1 ht.2.le
end YangMills.Construction.TwoPoints
end
