import YangMills.Construction.ReflectionPositivity.WeightsFormAndSeriesOfASplitTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies
def PerturbedReflMeasureInvariant : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (Λ : PeriodSublattice 1) (v : AmbientSpace) (hv : v ∈ normalSet) (k : ℤ),
    Λ.SplitsAlongWithHalfPeriod v k → ∀ (c : ℝ) (hc : IsAllowedLevel 1 v c),
      let P : NormalLevelPair 1 := ⟨v, hv, c, hc⟩
      ∀ E : Λ.QuotientField → ℝ, (fun U => (E U : ℂ)) ∈ Λ.plusAlgebra v k c →
        IsProbabilityMeasure (Λ.perturbedReflMeasure β P E) ∧
        PeriodSublattice.PreservesFiniteMeasure (Λ.pullbackField P.reflectSymmetry)
          (Λ.perturbedReflMeasure β P E)
end YangMills.Construction.InfiniteLattice
