import YangMills.Construction.InfiniteLattice.KernelsOfFiniteSetsOfBonds
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.AnyOrientationGibbs
variable {a : ℝ}
def PreservesContinuousLocal (β : ℝ) (ν : Measure (GaugeField a)) : Prop :=
  ∀ (S : Finset (Link a)) (h : HasNoOppositePairs (S : Set (Link a))),
    ∀ F ∈ continuousLocal a,
      ∫ U, wilsonLinkKernel β S h F U ∂ν = ∫ U, F U ∂ν
def PreservesBoundedMeasurable (β : ℝ) (ν : Measure (GaugeField a)) : Prop :=
  ∀ (S : Finset (Link a)) (h : HasNoOppositePairs (S : Set (Link a)))
    (F : GaugeField a → ℂ), IsBoundedObservable F →
      ∫ U, wilsonLinkKernel β S h F U ∂ν = ∫ U, F U ∂ν
def Equivalences : Prop :=
  ∀ (a β : ℝ), 0 < a → 0 < β → ∀ ν : Measure (GaugeField a), IsProbabilityMeasure ν →
    List.TFAE [IsGibbs β ν, PreservesContinuousLocal β ν,
      PreservesBoundedMeasurable β ν]
end YangMills.Construction.GibbsAtFixedSpacing.AnyOrientationGibbs
