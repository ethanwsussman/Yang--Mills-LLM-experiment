import YangMills.Construction.Functions.BoundsOfTheSmearingFilterAndWeight
import YangMills.Construction.ReflectionPositivity.CubeAndCubeVectors
import YangMills.Construction.ReflectionPositivity.EnergyMomentumMeasuresOfTheSiteAndLinkPictures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.ReflectionPositivity.EnergyMomentum
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.InfiniteLattice (GaugeField)
open YangMills.Construction.SmearingFilter (weightSeries absCoeffSum)
open YangMills.Construction.SmearingFilter.Bounds (WeightProperties)
def momentumProj (μ : Fin 4) (x : SpectralSpace μ) : DualTorus μ :=
  torusProj μ x.momentum
theorem continuous_momentumProj (μ : Fin 4) : Continuous (momentumProj μ) := by
  have e : momentumProj μ =
      (toCircles μ).symm ∘ Prod.snd ∘ chartHomeomorph μ := by
    funext x
    apply (toCircles μ).injective
    funext l
    simp [momentumProj, toCircles_torusProj, chartHomeomorph, chart]
    rfl
  rw [e]
  exact (toCircles μ).symm.continuous.comp
    (continuous_snd.comp (chartHomeomorph μ).continuous)
theorem measurable_momentumProj (μ : Fin 4) : Measurable (momentumProj μ) :=
  (continuous_momentumProj μ).measurable
def smearedEnergyDensity (μ : Fin 4) (r : ℕ+) (x : SpectralSpace μ) : ℝ :=
  (weightSeries (expNegNatMulEnergy (2 * (r : ℕ)) x.energy)).re
theorem expNegNatMulEnergy_mem_Icc (n : ℕ) (E : ENNReal) :
    expNegNatMulEnergy n E ∈ Icc (0 : ℝ) 1 :=
  ⟨pow_nonneg (expNegEnergy E).2.1 n, pow_le_one₀ (expNegEnergy E).2.1 (expNegEnergy E).2.2⟩
theorem ofReal_smearedEnergyDensity (hW : WeightProperties) (μ : Fin 4) (r : ℕ+)
    (x : SpectralSpace μ) :
    (smearedEnergyDensity μ r x : ℂ) = weightSeries (expNegNatMulEnergy (2 * (r : ℕ)) x.energy) :=
  Complex.ext rfl (by
    simpa [smearedEnergyDensity] using
      ((hW.2.1 _ (expNegNatMulEnergy_mem_Icc (2 * (r : ℕ)) x.energy)).1).symm)
theorem smearedEnergyDensity_nonneg (hW : WeightProperties) (μ : Fin 4) (r : ℕ+)
    (x : SpectralSpace μ) :
    0 ≤ smearedEnergyDensity μ r x :=
  (hW.2.1 _ (expNegNatMulEnergy_mem_Icc (2 * (r : ℕ)) x.energy)).2.1
theorem smearedEnergyDensity_le (hW : WeightProperties) (μ : Fin 4) (r : ℕ+)
    (x : SpectralSpace μ) :
    smearedEnergyDensity μ r x ≤ 2 * absCoeffSum :=
  (hW.2.1 _ (expNegNatMulEnergy_mem_Icc (2 * (r : ℕ)) x.energy)).2.2
theorem continuous_expNegEnergy_energy (μ : Fin 4) :
    Continuous fun x : SpectralSpace μ => expNegEnergy x.energy :=
  continuous_fst.comp (chartHomeomorph μ).continuous
theorem measurable_smearedEnergyDensity (hW : WeightProperties) (μ : Fin 4) (r : ℕ+) :
    Measurable (smearedEnergyDensity μ r) := by
  have hc : Continuous fun t : unitInterval => (weightSeries (t : ℝ)).re :=
    Complex.continuous_re.comp (continuousOn_iff_continuous_domRestrict.mp hW.1)
  have e : smearedEnergyDensity μ r =
      (fun t : unitInterval => (weightSeries (t : ℝ)).re) ∘
        fun x : SpectralSpace μ => expNegEnergy x.energy ^ (2 * (r : ℕ)) := by
    funext x
    simp [smearedEnergyDensity, expNegNatMulEnergy]
  rw [e]
  exact (hc.comp ((continuous_expNegEnergy_energy μ).pow _)).measurable
def weightedMomentumLaw (μ : Fin 4) (r : ℕ+) (σ : Measure (SpectralSpace μ)) :
    Measure (DualTorus μ) :=
  (withDensityReal σ (smearedEnergyDensity μ r)).map (momentumProj μ)
theorem weightedMomentumLaw_apply (hW : WeightProperties) (μ : Fin 4) (r : ℕ+)
    (σ : Measure (SpectralSpace μ)) [IsFiniteMeasure σ] {S : Set (DualTorus μ)}
    (hS : MeasurableSet S) :
    weightedMomentumLaw μ r σ S =
      ENNReal.ofReal (∫ x, S.indicator 1 (momentumProj μ x) * smearedEnergyDensity μ r x ∂σ) := by
  rw [weightedMomentumLaw, Measure.map_apply (measurable_momentumProj μ) hS,
    withDensityReal_apply σ (measurable_smearedEnergyDensity hW μ r)
      (smearedEnergyDensity_nonneg hW μ r)
      (smearedEnergyDensity_le hW μ r) (measurable_momentumProj μ hS)]
  rfl
variable (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+)
def siteMomentumLaw (A : GaugeField (1 : ℝ) → ℂ) : Measure (DualTorus μ) :=
  weightedMomentumLaw μ r (siteSpectralMeasure ν μ (cubeVector ν μ r A))
end YangMills.Construction.ReflectionPositivity.DirectionPictures
