import YangMills.Construction.Functions.SmearingFilterWeight
import YangMills.Construction.ReflectionPositivity.SpectralVariablesAsASpaceAndTheMomentumTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmearingFilter.Bounds
open scoped ENNReal Real
open YangMills.Construction.SmearingFilter YangMills.Construction.TriangleKernel
open YangMills.Construction.ReflectionPositivity.EnergyMomentum (distTwoPiInt)
def FilterProperties : Prop :=
  (∀ u : ℝ, (filterSeries u).im = 0) ∧
  Continuous filterSeries ∧
  (∀ u : ℝ, filterSeries u =
    ((1 / 2 * tentFunction (u + π / 2) - tentFunction (u + π)
      + 1 / 2 * tentFunction (u - π / 2) : ℝ) : ℂ)) ∧
  (∀ u : ℝ, ‖filterSeries u‖ ≤ ⨆ v : ℝ, tentFunction v) ∧
  (⨆ v : ℝ, tentFunction v) = 8 ∧
  (∀ u : ℝ, distTwoPiInt u ≤ π / 4 → filterSeries u = 0)
def WeightProperties : Prop :=
  ContinuousOn weightSeries (Set.Icc 0 1) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1, (weightSeries t).im = 0 ∧ 0 ≤ (weightSeries t).re ∧
    (weightSeries t).re ≤ 2 * absCoeffSum) ∧
  weightSeries 1 = filterSeries 0 ∧
  filterSeries 0 = 0 ∧
  (∀ x : ℝ≥0∞, 0 < x → x < ∞ → (weightSeriesAtExp x).im = 0 ∧
    weightConst * Real.tanh x.toReal ≤ (weightSeriesAtExp x).re)
def FilterWeightBounds : Prop :=
  FilterProperties ∧ WeightProperties
end YangMills.Construction.SmearingFilter.Bounds
