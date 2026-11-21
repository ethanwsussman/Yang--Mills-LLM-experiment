import YangMills.Construction.ReflectionPositivity.ReflectionGroupAndCubeReflectionSize
import YangMills.Construction.ReflectionPositivity.SpectralDensityConstant
import YangMills.Construction.ReflectionPositivity.WeightedMomentumMeasureOfACubeVector
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (unitRegionObservables)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass siteReflect)
open YangMills.Construction.SmearingFilter (spectralDensityConst)
open YangMills.Construction.ReflectionPositivity.EnergyMomentum (DualTorus torusMeasure)
namespace MomentumDensityBound
def Statement : Prop :=
  0 < spectralDensityConst ∧
    ∀ (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+) (ς : ℤˣ),
      ∀ A ∈ unitRegionObservables (cubeOfRadius r),
        (siteReflect μ).actOn A = (fun U => ((ς : ℤ) : ℂ) * A U) →
        IsFiniteMeasure (siteMomentumLaw ν μ r A) ∧
          ∃ h : DualTorus μ → ℝ, Continuous h ∧
            siteMomentumLaw ν μ r A = withDensityReal (torusMeasure μ) h ∧
            ∀ η, 0 ≤ h η ∧
              h η ≤ spectralDensityConst * (r : ℝ) ^ 3 * cubeReflectionNorm ν r A
end MomentumDensityBound
end YangMills.Construction.ReflectionPositivity.DirectionPictures
end
