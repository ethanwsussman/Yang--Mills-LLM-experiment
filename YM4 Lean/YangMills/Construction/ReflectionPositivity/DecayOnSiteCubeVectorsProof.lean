import YangMills.Construction.ReflectionPositivity.BoundedMomentumDensityWithReflectionSizes
import YangMills.Construction.ReflectionPositivity.CubeVectorsDependLinearlyOnTheObservable
import YangMills.Construction.ReflectionPositivity.DecayFromABoundedWeightedDensityAndTheCone
import YangMills.Construction.ReflectionPositivity.DecayOnSiteCubeVectors
import YangMills.Construction.ReflectionPositivity.FormOfTransferPowerInAPicture
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (unitRegionObservables)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass siteReflect)
open YangMills.Construction.SmearingFilter (spectralRateConst weightSeries weightConst spectralDensityConst)
open YangMills.Construction.SmearingFilter.Bounds (WeightProperties)
open YangMills.Construction.ReflectionPositivity.EnergyMomentum
namespace CubeVectorDecay
theorem weightConst_mul_slopeConstant_pow_pos : 0 < weightConst * slopeConstant ^ 3 := by
  have hsqrt : 1 < √(2 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hw : 0 < weightConst := by
    unfold YangMills.Construction.SmearingFilter.weightConst
    linarith
  have hk : 0 < slopeConstant := by
    unfold slopeConstant
    have hlog : 0 < Real.log (1 + √(2 : ℝ)) := Real.log_pos (by linarith)
    have := Real.pi_pos
    positivity
  positivity
theorem setIntegral_weightSeries_eq_setIntegral_density (hW : WeightProperties) (μ : Fin 4) (r : ℕ+)
    (σ : Measure (SpectralSpace μ)) [IsFiniteMeasure σ] {g : DualTorus μ → ℝ}
    (hgm : Measurable g) (hg0 : ∀ η, 0 ≤ g η) {B : ℝ} (hgB : ∀ η, g η ≤ B)
    (hlaw : weightedMomentumLaw μ r σ = withDensityReal (torusMeasure μ) g)
    (S : Set (DualTorus μ)) (hS : MeasurableSet S) :
    ∫ x in (fun x : SpectralSpace μ => torusProj μ x.momentum) ⁻¹' S,
        weightSeries (expNegNatMulEnergy (2 * (r : ℕ)) x.energy) ∂σ =
      ∫ η in S, (g η : ℂ) ∂(torusMeasure μ) := by
  have happ := weightedMomentumLaw_apply hW μ r σ hS
  rw [hlaw, withDensityReal_apply (torusMeasure μ) hgm hg0 hgB hS] at happ
  have hleft : 0 ≤ ∫ η, S.indicator 1 η * g η ∂(torusMeasure μ) :=
    integral_nonneg fun η => mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) η) (hg0 η)
  have hright : 0 ≤ ∫ x, S.indicator 1 (momentumProj μ x) * smearedEnergyDensity μ r x ∂σ :=
    integral_nonneg fun x =>
      mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (smearedEnergyDensity_nonneg hW μ r x)
  have heq := (ENNReal.ofReal_eq_ofReal_iff hleft hright).1 happ
  have hpre : MeasurableSet ((fun x : SpectralSpace μ => torusProj μ x.momentum) ⁻¹' S) :=
    measurable_momentumProj μ hS
  have hlhs : ∫ x in (fun x : SpectralSpace μ => torusProj μ x.momentum) ⁻¹' S,
        weightSeries (expNegNatMulEnergy (2 * (r : ℕ)) x.energy) ∂σ =
      ((∫ x, S.indicator 1 (momentumProj μ x) * smearedEnergyDensity μ r x ∂σ : ℝ) : ℂ) := by
    rw [← integral_indicator hpre, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : momentumProj μ x ∈ S
    · have hx' : x ∈ (fun x : SpectralSpace μ => torusProj μ x.momentum) ⁻¹' S := hx
      simp only [indicator_of_mem hx, indicator_of_mem hx', Pi.one_apply, one_mul]
      exact (ofReal_smearedEnergyDensity hW μ r x).symm
    · have hx' : x ∉ (fun x : SpectralSpace μ => torusProj μ x.momentum) ⁻¹' S := hx
      simp only [indicator_of_notMem hx, indicator_of_notMem hx', zero_mul, Complex.ofReal_zero]
  have hrhs : ∫ η in S, (g η : ℂ) ∂(torusMeasure μ) =
      ((∫ η, S.indicator 1 η * g η ∂(torusMeasure μ) : ℝ) : ℂ) := by
    rw [← integral_indicator hS, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun η => ?_)
    by_cases hη : η ∈ S
    · simp [indicator_of_mem hη]
    · simp [indicator_of_notMem hη]
  rw [hlhs, hrhs, heq]
theorem powerOffGroundForm_re_le_of_parity (hW : WeightProperties)
    (hspec : SpectralMeasuresTheorem)
    (hsite : SiteReflectionPair.Conclusion)
    (hdens : MomentumDensityBound.Statement)
    (hpow : PowerOffGround.Holds)
    (hcone : ConeDecayTheorem)
    (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+) (s : ℤˣ)
    {A : InfiniteLattice.GaugeField (1 : ℝ) → ℂ} (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hrefl : (siteReflect μ).actOn A = (fun U => ((s : ℤ) : ℂ) * A U))
    (n : ℕ) (hn : 1 ≤ n) :
    (ReflectionPair.site.powerOffGroundForm ν μ n (cubeVector ν μ r A) (cubeVector ν μ r A)).re ≤
      48 * (spectralDensityConst / (weightConst * slopeConstant ^ 3)) *
        ((((r : ℕ) : ℝ) / (n : ℝ)) ^ 2 + (((r : ℕ) : ℝ) / (n : ℝ)) ^ 3) *
        cubeReflectionNorm ν r A := by
  obtain ⟨hspace, -, hpairs⟩ := hspec μ
  obtain ⟨-, -, -, -, -, -, hclosed, -, -, hE, -⟩ := hspace
  obtain ⟨-, -, -, -, -, -, hsupp, -, -⟩ := hpairs ν ReflectionPair.site
  obtain ⟨hC, hbound⟩ := hdens
  obtain ⟨-, g, hgc, hglaw, hgb⟩ := hbound ν μ r s A hA hrefl
  have hD := weightConst_mul_slopeConstant_pow_pos
  have hr : (0 : ℝ) < ((r : ℕ) : ℝ) := by exact_mod_cast r.pos
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hB0 : 0 ≤ spectralDensityConst * ((r : ℕ) : ℝ) ^ 3 * cubeReflectionNorm ν r A :=
    (hgb 0).1.trans (hgb 0).2
  have hnorm : 0 ≤ cubeReflectionNorm ν r A :=
    (mul_nonneg_iff_of_pos_left (by positivity)).1 hB0
  have hdecay := hcone μ (r : ℕ) n _ r.pos hn hB0
    (ReflectionPair.site.spectralMeasure ν μ (cubeVector ν μ r A)) (coneInSpectral μ) g
    hclosed.measurableSet (hsupp _)
    (fun x hx hfin => (((hsite ν μ r).2.1.2.1 x.1 hx).2 hfin.ne).2)
    hgc.measurable hgb
    (fun S hS => setIntegral_weightSeries_eq_setIntegral_density hW μ r _ hgc.measurable
      (fun η => (hgb η).1) (fun η => (hgb η).2) hglaw S hS)
  have hmeas : MeasurableSet (PowerOffGround.excitedSet μ) :=
    (measurableSet_lt measurable_const hE).inter (measurableSet_lt hE measurable_const)
  have hform := ((((hpow ν μ n hn).2 ReflectionPair.site).1).2 (cubeVector ν μ r A)).2
  rw [hform, Complex.ofReal_re, integral_indicator hmeas]
  refine hdecay.trans ?_
  set D := weightConst * slopeConstant ^ 3 with hDdef
  set N := cubeReflectionNorm ν r A with hNdef
  set C := spectralDensityConst with hCdef
  set R := ((r : ℕ) : ℝ) with hRdef
  set M := (n : ℝ) with hMdef
  have hrw : C * R ^ 3 * N / D * (48 / M ^ 3 + 12 / (R * M ^ 2)) =
      C / D * N * (48 * (R / M) ^ 3 + 12 * (R / M) ^ 2) := by
    field_simp
  rw [hrw]
  have hCDN : 0 ≤ C / D * N := by positivity
  have hq : 0 ≤ R / M := by positivity
  have hpoly : 48 * (R / M) ^ 3 + 12 * (R / M) ^ 2 ≤ 48 * ((R / M) ^ 2 + (R / M) ^ 3) := by
    nlinarith [pow_nonneg hq 2]
  calc C / D * N * (48 * (R / M) ^ 3 + 12 * (R / M) ^ 2)
      ≤ C / D * N * (48 * ((R / M) ^ 2 + (R / M) ^ 3)) :=
        mul_le_mul_of_nonneg_left hpoly hCDN
    _ = 48 * (C / D) * ((R / M) ^ 2 + (R / M) ^ 3) * N := by ring
theorem of_spectral_bounds
    (hsite : SiteReflectionPair.Conclusion)
    (hweight : YangMills.Construction.SmearingFilter.Bounds.FilterWeightBounds)
    (hspec : SpectralMeasuresTheorem)
    (hdens : MomentumDensityBound.Statement)
    (hpow : PowerOffGround.Holds)
    (hlin : CubeVectorLinearity.Statement)
    (hcone : ConeDecayTheorem) :
    CubeVectorDecay := by
  have hW : WeightProperties := hweight.2
  have hD := weightConst_mul_slopeConstant_pow_pos
  have hC : 0 < spectralDensityConst := hdens.1
  refine ⟨by unfold YangMills.Construction.SmearingFilter.spectralRateConst; positivity, ?_⟩
  intro ν μ r A hA n hn
  obtain ⟨-, -, hparts⟩ := (hlin ν μ r).1
  obtain ⟨hAe, hAo, hre, hro, hsplit, hNe, hNo⟩ := hparts A hA
  have he := powerOffGroundForm_re_le_of_parity hW hspec hsite hdens hpow hcone ν μ r 1 hAe
    (by rw [hre]; funext U; simp) n hn
  have ho := powerOffGroundForm_re_le_of_parity hW hspec hsite hdens hpow hcone ν μ r (-1) hAo
    (by rw [hro]; funext U; simp) n hn
  have hsum := (((hpow ν μ n hn).2 ReflectionPair.site).2.2.1.2.2
    (cubeVector ν μ r (evenPartUnder (siteReflect μ) A))
    (cubeVector ν μ r (oddPartUnder (siteReflect μ) A))).2
  rw [← hsplit] at hsum
  have hform := ((((hpow ν μ n hn).2 ReflectionPair.site).1).2 (cubeVector ν μ r A)).2
  have hI : 0 ≤ integral (ReflectionPair.site.spectralMeasure ν μ (cubeVector ν μ r A))
      ((PowerOffGround.excitedSet μ).indicator
        fun y : SpectralSpace μ => expNegNatMulEnergy n y.energy) :=
    integral_nonneg fun x =>
      indicator_nonneg (fun y _ => (expNegNatMulEnergy_mem_Icc n y.energy).1) x
  rw [hform, Complex.ofReal_re] at hsum
  change 0 ≤ ReflectionPair.site.powerOffGroundForm ν μ n _ _ ∧
    ReflectionPair.site.powerOffGroundForm ν μ n _ _ ≤ _
  rw [hform]
  refine ⟨Complex.zero_le_real.2 hI, Complex.real_le_real.2 (hsum.trans ?_)⟩
  have hr : (0 : ℝ) < ((r : ℕ) : ℝ) := by exact_mod_cast r.pos
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hQ : 0 ≤ 48 * (spectralDensityConst / (weightConst * slopeConstant ^ 3)) *
      ((((r : ℕ) : ℝ) / (n : ℝ)) ^ 2 + (((r : ℕ) : ℝ) / (n : ℝ)) ^ 3) := by positivity
  have he' := he.trans (mul_le_mul_of_nonneg_left hNe hQ)
  have ho' := ho.trans (mul_le_mul_of_nonneg_left hNo hQ)
  have hrw : spectralRateConst *
      ((((r : ℕ) : ℝ) / (n : ℝ)) ^ 2 + (((r : ℕ) : ℝ) / (n : ℝ)) ^ 3) *
      cubeReflectionNorm ν r A =
      2 * (48 * (spectralDensityConst / (weightConst * slopeConstant ^ 3)) *
        ((((r : ℕ) : ℝ) / (n : ℝ)) ^ 2 + (((r : ℕ) : ℝ) / (n : ℝ)) ^ 3) *
        cubeReflectionNorm ν r A) +
      2 * (48 * (spectralDensityConst / (weightConst * slopeConstant ^ 3)) *
        ((((r : ℕ) : ℝ) / (n : ℝ)) ^ 2 + (((r : ℕ) : ℝ) / (n : ℝ)) ^ 3) *
        cubeReflectionNorm ν r A) := by
    unfold YangMills.Construction.SmearingFilter.spectralRateConst
    ring
  rw [hrw]
  linarith
end CubeVectorDecay
end YangMills.Construction.ReflectionPositivity.DirectionPictures
