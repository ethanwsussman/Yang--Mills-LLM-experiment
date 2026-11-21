import YangMills.Construction.ReflectionPositivity.TwoPicturesOfADirection
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint axisStep shift halfSpaceLocalObservables)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass siteReflect)
def MultiStepInequalities : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4) (t : TransverseAxis μ) (k : ℕ), 1 ≤ k →
    (1 - ReflectionPair.site.transferOp ν μ ^ k) ^ 2 ≥
      ReflectionPair.site.transferOp ν μ ^ k *
        ((2 : ℂ) • 1 - ReflectionPair.site.shiftOp ν μ t ^ k -
          star (ReflectionPair.site.shiftOp ν μ t) ^ k) ∧
    ∀ F ∈ halfSpaceLocalObservables μ,
      let u : LatticePoint (1 : ℝ) → ℂ := fun v =>
        ∫ U, conj ((siteReflect μ).actOn F U) * (shift v).actOn F U
          ∂(ν : Measure (GaugeField (1 : ℝ)))
      0 ≤ u 0 - 4 * u (k • axisStep (1 : ℝ) μ) + u ((2 * k) • axisStep (1 : ℝ) μ) +
        u (k • axisStep (1 : ℝ) μ + k • axisStep (1 : ℝ) t.1) +
        u (k • axisStep (1 : ℝ) μ - k • axisStep (1 : ℝ) t.1)
end YangMills.Construction.ReflectionPositivity.DirectionPictures
