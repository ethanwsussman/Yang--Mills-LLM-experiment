import YangMills.Construction.Functions.SmearingFilterWeight
import YangMills.Construction.ReflectionPositivity.SpectralVariablesAsASpaceAndTheMomentumTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.EnergyMomentum
open YangMills.Construction.ReflectionPositivity.DirectionPictures (slopeConstant angleSupNorm)
def ConeDecayTheorem : Prop :=
  ∀ (μ : Fin 4) (r n : ℕ) (H : ℝ), 1 ≤ r → 1 ≤ n → 0 ≤ H →
    ∀ (m : Measure (SpectralSpace μ)) [IsFiniteMeasure m]
      (C : Set (SpectralSpace μ)) (g : DualTorus μ → ℝ),
      MeasurableSet C → m Cᶜ = 0 →
      (∀ x ∈ C, x.energy < ∞ → slopeConstant * angleSupNorm μ x.momentum ≤ x.energy.toReal) →
      Measurable g → (∀ η, 0 ≤ g η ∧ g η ≤ H) →
      (∀ S : Set (DualTorus μ), MeasurableSet S →
        ∫ x in (fun x : SpectralSpace μ => torusProj μ x.momentum) ⁻¹' S,
            YangMills.Construction.SmearingFilter.weightSeries
              (expNegNatMulEnergy (2 * r) x.energy) ∂m =
          ∫ η in S, (g η : ℂ) ∂(torusMeasure μ)) →
      ∫ x in {x : SpectralSpace μ | 0 < x.energy ∧ x.energy < ∞},
          expNegNatMulEnergy n x.energy ∂m ≤
        H / (YangMills.Construction.SmearingFilter.weightConst * slopeConstant ^ 3) *
          (48 / (n : ℝ) ^ 3 + 12 / ((r : ℝ) * (n : ℝ) ^ 2))
end YangMills.Construction.ReflectionPositivity.EnergyMomentum
