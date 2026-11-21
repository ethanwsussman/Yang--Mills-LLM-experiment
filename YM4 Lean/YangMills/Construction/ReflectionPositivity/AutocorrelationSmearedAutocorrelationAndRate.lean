import YangMills.Construction.Functions.TriangleKernel
import YangMills.Construction.ReflectionPositivity.SpectralVariablesAsASpaceAndTheMomentumTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Real
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.Autocorrelation
open YangMills.Construction.InfiniteLattice (GaugeField axisStep shift)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.ReflectionPositivity.DirectionPictures (slopeConstant intPoint)
open YangMills.Construction.ReflectionPositivity.EnergyMomentum (orthLattice)
open YangMills.Construction.TriangleKernel (smearingSeq tentFourierCoeff)
def twoPointCorrelation (ν : unitPositiveClass) (μ : Fin 4) (ς : ℤˣ)
    (A : GaugeField (1 : ℝ) → ℂ) (s : ℤ) (w : orthLattice μ) : ℂ :=
  ((ς : ℤ) : ℂ) * ∫ U, starRingEnd ℂ (A U) *
    (shift (s • axisStep (1 : ℝ) μ + intPoint w.1)).actOn A U ∂ν.1
def smearedTwoPointCorrelation (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+) (ς : ℤˣ)
    (A : GaugeField (1 : ℝ) → ℂ) (w : orthLattice μ) : ℂ :=
  ∑' j : ℤ, (smearingSeq j : ℂ) * tentFourierCoeff j *
    twoPointCorrelation ν μ ς A (2 * (r : ℤ) * j) w
def correlationDecayRate (r : ℕ+) : ℝ := slopeConstant * π / (8 * (r : ℝ))
end YangMills.Construction.ReflectionPositivity.Autocorrelation
