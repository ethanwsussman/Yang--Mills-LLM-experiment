import YangMills.Construction.InfiniteLattice.GibbsKernelAndPeriodicGibbsStatesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.ObservablesOfTheUnitLatticeAndItsHalfSpaces
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open MeasureTheory
open YangMills.Construction.GibbsAtFixedSpacing
def UnitGibbsKernelRules : Prop :=
  ∀ β : ℝ, 0 < β →
    (∀ (W : Finset (Link (1 : ℝ)))
        (hW : HasNoOppositePairs (W : Set (Link (1 : ℝ))))
        (F : GaugeField (1 : ℝ) → ℂ), IsBoundedObservable F →
      (IsBoundedObservable (gibbsKernelUnit β W hW F) ∧
        (∀ G : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable G → ∀ c d : ℂ,
          gibbsKernelUnit β W hW (c • F + d • G) =
            c • gibbsKernelUnit β W hW F + d • gibbsKernelUnit β W hW G) ∧
        observableSupNorm (gibbsKernelUnit β W hW F) ≤ observableSupNorm F) ∧
      (∀ S : Set AmbientSpace, (∀ ℓ ∈ W, ¬ ℓ.IsWithin S) → ∀ H ∈ unitRegionObservables S,
        gibbsKernelUnit β W hW (H * F) = H * gibbsKernelUnit β W hW F)) ∧
    (∀ ν : Measure (GaugeField (1 : ℝ)), IsProbabilityMeasure ν →
      (IsGibbs β ν ↔
        ∀ (W' : Finset (Link (1 : ℝ)))
          (hW' : HasNoOppositePairs (W' : Set (Link (1 : ℝ)))),
          ∀ F' ∈ continuousLocalFunctions (1 : ℝ),
            ∫ U, gibbsKernelUnit β W' hW' F' U ∂ν = ∫ U, F' U ∂ν))
end YangMills.Construction.InfiniteLattice
