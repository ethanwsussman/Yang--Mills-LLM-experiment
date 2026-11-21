import YangMills.Construction.InfiniteLattice.PureAndErgodicMeasuresOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.ShiftInvariantConditioningAndPlateau
import YangMills.Construction.ReflectionPositivity.RateConstantAndRateFunction
import YangMills.Construction.ReflectionPositivity.ReflectionGroupAndCubeReflectionSize
import YangMills.Construction.ReflectionPositivity.SpectralVariablesAsASpaceAndTheMomentumTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open InfiniteLattice (GaugeField IsUnitShiftErgodic shiftInvariantSigma shift
  unitRegionObservables plateauUnitSpacing)
open MirrorHyperplanes (unitPositiveClass)
open SmearingFilter (spectralRateFn)
def cubeGap (r : ℕ+) (y : Fin 4 → ℤ) : ℝ :=
  EnergyMomentum.supNormCoord (fun i => (y i : ℝ)) - 2 * (r : ℝ)
def InverseSquareClustering : Prop :=
  ∀ (ν : unitPositiveClass) (r : ℕ+),
    ∀ A ∈ unitRegionObservables (cubeOfRadius r), ∀ B ∈ unitRegionObservables (cubeOfRadius r),
      (∀ y : Fin 4 → ℤ, 1 ≤ cubeGap r y →
        ‖(∫ U, conj (A U) * (shift (intPoint y)).actOn B U
            ∂(ν : Measure (GaugeField (1 : ℝ)))) -
          plateauUnitSpacing (ν : Measure (GaugeField (1 : ℝ))) A B‖ ≤
        spectralRateFn ((r : ℝ) / cubeGap r y) *
          cubeReflectionNorm ν r A ^ (1 / 2 : ℝ) * cubeReflectionNorm ν r B ^ (1 / 2 : ℝ)) ∧
      (IsUnitShiftErgodic (ν : Measure (GaugeField (1 : ℝ))) →
        plateauUnitSpacing (ν : Measure (GaugeField (1 : ℝ))) A B =
          conj (∫ U, A U ∂(ν : Measure (GaugeField (1 : ℝ)))) *
            ∫ U, B U ∂(ν : Measure (GaugeField (1 : ℝ))))
end YangMills.Construction.ReflectionPositivity.DirectionPictures
end
